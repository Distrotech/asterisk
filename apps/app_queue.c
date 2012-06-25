/*
 * Asterisk -- An open source telephony toolkit.
 *
 * Copyright (C) 1999 - 2006, Digium, Inc.
 *
 * Mark Spencer <markster@digium.com>
 *
 * See http://www.asterisk.org for more information about
 * the Asterisk project. Please do not directly contact
 * any of the maintainers of this project for assistance;
 * the project provides a web site, mailing lists and IRC
 * channels for your use.
 *
 * This program is free software, distributed under the terms of
 * the GNU General Public License Version 2. See the LICENSE file
 * at the top of the source tree.
 */

/*! \file
 *
 * \brief True call queues with optional send URL on answer
 *
 * \author Mark Spencer <markster@digium.com>
 *
 * \arg Config in \ref Config_qu queues.conf
 *
 * \par Development notes
 * \note 2011-11-01: Reworked to seperate structures make more thread safe
 *		Distrotech PTY (LTD) (www.distrotech.co.za)
 *		Gregory Nietsky (irroot) <gregory@distrotech.co.za>
 *
 *		Split away from locking queues/queue to having locks per
 *		Queue Data/Member/Device.
 *		Added device state struct to mange device states shared
 *		for multiple members sharing same device.
 *		Added queue data struct to mange queue data.
 *
 *		Made all functions work with realtime/dynamic/static members.
 *		Added missing CLI/AMI functions for handling callinuse (ignorebusy).
 *
 * \note 2004-11-25: Persistent Dynamic Members added by:
 *             NetNation Communications (www.netnation.com)
 *             Kevin Lindsay <kevinl@netnation.com>
 *
 *             Each dynamic agent in each queue is now stored in the astdb.
 *             When asterisk is restarted, each agent will be automatically
 *             readded into their recorded queues. This feature can be
 *             configured with the 'persistent_members=<1|0>' setting in the
 *             '[general]' category in queues.conf. The default is on.
 *
 * \note 2004-06-04: Priorities in queues added by inAccess Networks (work funded by Hellas On Line (HOL) www.hol.gr).
 *
 * \note These features added by David C. Troy <dave@toad.net>:
 *    - Per-queue holdtime calculation
 *    - Estimated holdtime announcement
 *    - Position announcement
 *    - Abandoned/completed call counters
 *    - Failout timer passed as optional app parameter
 *    - Optional monitoring of calls, started when call is answered
 *
 * Patch Version 1.07 2003-12-24 01
 *
 * Added servicelevel statistic by Michiel Betel <michiel@betel.nl>
 * Added Priority jumping code for adding and removing queue members by Jonathan Stanton <asterisk@doilooklikeicare.com>
 *
 * Fixed to work with CVS as of 2004-02-25 and released as 1.07a
 * by Matthew Enger <m.enger@xi.com.au>
 *
 * \ingroup applications
 */

/*** MODULEINFO
	<use type="module">res_monitor</use>
	<support_level>core</support_level>
 ***/

#include "asterisk.h"

ASTERISK_FILE_VERSION(__FILE__, "$Revision$")

#include <sys/time.h>
#include <sys/signal.h>
#include <netinet/in.h>
#include <ctype.h>

#include "asterisk/lock.h"
#include "asterisk/file.h"
#include "asterisk/channel.h"
#include "asterisk/pbx.h"
#include "asterisk/app.h"
#include "asterisk/linkedlists.h"
#include "asterisk/module.h"
#include "asterisk/translate.h"
#include "asterisk/say.h"
#include "asterisk/features.h"
#include "asterisk/musiconhold.h"
#include "asterisk/cli.h"
#include "asterisk/manager.h"
#include "asterisk/config.h"
#include "asterisk/monitor.h"
#include "asterisk/utils.h"
#include "asterisk/causes.h"
#include "asterisk/astdb.h"
#include "asterisk/devicestate.h"
#include "asterisk/stringfields.h"
#include "asterisk/event.h"
#include "asterisk/astobj2.h"
#include "asterisk/strings.h"
#include "asterisk/global_datastores.h"
#include "asterisk/taskprocessor.h"
#include "asterisk/aoc.h"
#include "asterisk/callerid.h"
#include "asterisk/cel.h"
#include "asterisk/data.h"
#include "asterisk/time.h"

/*!
 * \par Please read before modifying this file.
 * There are locks which are regularly used
 * throughout this file, the lock
 * for each individual queue, queue data, the individual member lock ,
 * and the device state lock.
 * there are container locks for the queues list, the member
 * list on each queue the devices container and rules container.
 * in the queue data struct there is linked lists for the entries in queue.
 * Please be extra careful to always lock in the following order
 *
 * 1) container lock first
 * 2) container element
 *
 * Never call a function on a container while a element is locked
 *
 * This order has sort of "evolved" over the lifetime of this
 * application, but it is now in place this way, so please adhere
 * to this order!
 *
 */

/*** DOCUMENTATION
	<application name="Queue" language="en_US">
		<synopsis>
			Queue a call for a call queue.
		</synopsis>
		<syntax>
			<parameter name="queuename" required="true" />
			<parameter name="options">
				<optionlist>
					<option name="C">
						<para>Mark all calls as "answered elsewhere" when cancelled.</para>
					</option>
					<option name="c">
						<para>Continue in the dialplan if the callee hangs up.</para>
					</option>
					<option name="d">
						<para>data-quality (modem) call (minimum delay).</para>
					</option>
					<option name="h">
						<para>Allow <emphasis>callee</emphasis> to hang up by pressing <literal>*</literal>.</para>
					</option>
					<option name="H">
						<para>Allow <emphasis>caller</emphasis> to hang up by pressing <literal>*</literal>.</para>
					</option>
					<option name="n">
						<para>No retries on the timeout; will exit this application and
						go to the next step.</para>
					</option>
					<option name="i">
						<para>Ignore call forward requests from queue members and do nothing
						when they are requested.</para>
					</option>
					<option name="I">
						<para>Asterisk will ignore any connected line update requests or any redirecting party
						update requests it may receive on this dial attempt.</para>
					</option>
					<option name="r">
						<para>Ring instead of playing MOH. Periodic Announcements are still made, if applicable.</para>
					</option>
					<option name="R">
						<para>Ring instead of playing MOH when a member channel is actually ringing.</para>
					</option>
					<option name="t">
						<para>Allow the <emphasis>called</emphasis> user to transfer the calling user.</para>
					</option>
					<option name="T">
						<para>Allow the <emphasis>calling</emphasis> user to transfer the call.</para>
					</option>
					<option name="w">
						<para>Allow the <emphasis>called</emphasis> user to write the conversation to
						disk via Monitor.</para>
					</option>
					<option name="W">
						<para>Allow the <emphasis>calling</emphasis> user to write the conversation to
						disk via Monitor.</para>
					</option>
					<option name="k">
						<para>Allow the <emphasis>called</emphasis> party to enable parking of the call by sending
						the DTMF sequence defined for call parking in <filename>features.conf</filename>.</para>
					</option>
					<option name="K">
						<para>Allow the <emphasis>calling</emphasis> party to enable parking of the call by sending
						the DTMF sequence defined for call parking in <filename>features.conf</filename>.</para>
					</option>
					<option name="x">
						<para>Allow the <emphasis>called</emphasis> user to write the conversation
						to disk via MixMonitor.</para>
					</option>
					<option name="X">
						<para>Allow the <emphasis>calling</emphasis> user to write the conversation to
						disk via MixMonitor.</para>
					</option>
				</optionlist>
			</parameter>
			<parameter name="URL">
				<para><replaceable>URL</replaceable> will be sent to the called party if the channel supports it.</para>
			</parameter>
			<parameter name="announceoverride" />
			<parameter name="timeout">
				<para>Will cause the queue to fail out after a specified number of
				seconds, checked between each <filename>queues.conf</filename> <replaceable>timeout</replaceable> and
				<replaceable>retry</replaceable> cycle.</para>
			</parameter>
			<parameter name="AGI">
				<para>Will setup an AGI script to be executed on the calling party's channel once they are
				connected to a queue member.</para>
			</parameter>
			<parameter name="macro">
				<para>Will run a macro on the calling party's channel once they are connected to a queue member.</para>
			</parameter>
			<parameter name="gosub">
				<para>Will run a gosub on the calling party's channel once they are connected to a queue member.</para>
			</parameter>
			<parameter name="rule">
				<para>Will cause the queue's defaultrule to be overridden by the rule specified.</para>
			</parameter>
			<parameter name="position">
				<para>Attempt to enter the caller into the queue at the numerical position specified. <literal>1</literal>
				would attempt to enter the caller at the head of the queue, and <literal>3</literal> would attempt to place
				the caller third in the queue.</para>
			</parameter>
		</syntax>
		<description>
			<para>In addition to transferring the call, a call may be parked and then picked
			up by another user.</para>
			<para>This application will return to the dialplan if the queue does not exist, or
			any of the join options cause the caller to not enter the queue.</para>
			<para>This application does not automatically answer and should be preceeded
			by an application such as Answer(), Progress(), or Ringing().</para>
			<para>This application sets the following channel variable upon completion:</para>
			<variablelist>
				<variable name="QUEUESTATUS">
					<para>The status of the call as a text string.</para>
					<value name="TIMEOUT" />
					<value name="FULL" />
					<value name="JOINEMPTY" />
					<value name="LEAVEEMPTY" />
					<value name="JOINUNAVAIL" />
					<value name="LEAVEUNAVAIL" />
					<value name="CONTINUE" />
				</variable>
			</variablelist>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</application>
	<application name="AddQueueMember" language="en_US">
		<synopsis>
			Dynamically adds queue members.
		</synopsis>
		<syntax>
			<parameter name="queuename" required="true" />
			<parameter name="interface" />
			<parameter name="penalty" />
			<parameter name="paused" />
			<parameter name="membername" />
			<parameter name="stateinterface" />
			<parameter name="callinuse" />
		</syntax>
		<description>
			<para>Dynamically adds interface to an existing queue. If the interface is
			already in the queue it will return an error.</para>
			<para>This application sets the following channel variable upon completion:</para>
			<variablelist>
				<variable name="AQMSTATUS">
					<para>The status of the attempt to add a queue member as a text string.</para>
					<value name="ADDED" />
					<value name="MEMBERALREADY" />
					<value name="NOSUCHQUEUE" />
				</variable>
			</variablelist>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</application>
	<application name="RemoveQueueMember" language="en_US">
		<synopsis>
			Dynamically removes queue members.
		</synopsis>
		<syntax>
			<parameter name="queuename" required="true" />
			<parameter name="interface" />
			<parameter name="options" />
		</syntax>
		<description>
			<para>If the interface is <emphasis>NOT</emphasis> in the queue it will return an error.</para>
			<para>This application sets the following channel variable upon completion:</para>
			<variablelist>
				<variable name="RQMSTATUS">
					<value name="REMOVED" />
					<value name="NOTINQUEUE" />
					<value name="NOSUCHQUEUE" />
				</variable>
			</variablelist>
			<para>Example: RemoveQueueMember(techsupport,SIP/3000)</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</application>
	<application name="PauseQueueMember" language="en_US">
		<synopsis>
			Pauses a queue member.
		</synopsis>
		<syntax>
			<parameter name="queuename" />
			<parameter name="interface" required="true" />
			<parameter name="options" />
			<parameter name="reason">
				<para>Is used to add extra information to the appropriate queue_log entries and manager events.</para>
			</parameter>
		</syntax>
		<description>
			<para>Pauses (blocks calls for) a queue member. The given interface will be paused in the given queue.
			This prevents any calls from being sent from the queue to the interface until it is
			unpaused with UnpauseQueueMember or the manager interface.  If no queuename is given,
			the interface is paused in every queue it is a member of. The application will fail if the
			interface is not found.</para>
			<para>This application sets the following channel variable upon completion:</para>
			<variablelist>
				<variable name="PQMSTATUS">
					<para>The status of the attempt to pause a queue member as a text string.</para>
					<value name="PAUSED" />
					<value name="NOTFOUND" />
				</variable>
			</variablelist>
			<para>Example: PauseQueueMember(,SIP/3000)</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</application>
	<application name="UnpauseQueueMember" language="en_US">
		<synopsis>
			Unpauses a queue member.		
		</synopsis>
		<syntax>
			<parameter name="queuename" />
			<parameter name="interface" required="true" />
			<parameter name="options" />
			<parameter name="reason">
				<para>Is used to add extra information to the appropriate queue_log entries and manager events.</para>
			</parameter>
		</syntax>
		<description>
			<para>Unpauses (resumes calls to) a queue member. This is the counterpart to <literal>PauseQueueMember()</literal>
			and operates exactly the same way, except it unpauses instead of pausing the given interface.</para>
			<para>This application sets the following channel variable upon completion:</para>
			<variablelist>
				<variable name="UPQMSTATUS">
					<para>The status of the attempt to unpause a queue member as a text string.</para>
					<value name="UNPAUSED" />
					<value name="NOTFOUND" />
				</variable>
			</variablelist>
			<para>Example: UnpauseQueueMember(,SIP/3000)</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</application>
	<application name="QueueLog" language="en_US">
		<synopsis>
			Writes to the queue_log file.
		</synopsis>
		<syntax>
			<parameter name="queuename" required="true" />
			<parameter name="uniqueid" required="true" />
			<parameter name="agent" required="true" />
			<parameter name="event" required="true" />
			<parameter name="additionalinfo" />
		</syntax>
		<description>
			<para>Allows you to write your own events into the queue log.</para>
			<para>Example: QueueLog(101,${UNIQUEID},${AGENT},WENTONBREAK,600)</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</application>
	<function name="QUEUE_VARIABLES" language="en_US">
		<synopsis>
			Return Queue information in variables.
		</synopsis>
		<syntax>
			<parameter name="queuename" required="true">
				<enumlist>
					<enum name="QUEUEMAX">
						<para>Maxmimum number of calls allowed.</para>
					</enum>
					<enum name="QUEUESTRATEGY">
						<para>The strategy of the queue.</para>
					</enum>
					<enum name="QUEUECALLS">
						<para>Number of calls currently in the queue.</para>
					</enum>
					<enum name="QUEUEHOLDTIME">
						<para>Current average hold time.</para>
					</enum>
					<enum name="QUEUECOMPLETED">
						<para>Number of completed calls for the queue.</para>
					</enum>
					<enum name="QUEUEABANDONED">
						<para>Number of abandoned calls.</para>
					</enum>
					<enum name="QUEUESRVLEVEL">
						<para>Queue service level.</para>
					</enum>
					<enum name="QUEUESRVLEVELPERF">
						<para>Current service level performance.</para>
					</enum>
				</enumlist>
			</parameter>
		</syntax>
		<description>
			<para>Makes the following queue variables available.</para>
			<para>Returns <literal>0</literal> if queue is found and setqueuevar is defined, <literal>-1</literal> otherwise.</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</function>
	<function name="QUEUE_MEMBER" language="en_US">
		<synopsis>
			Count number of members answering a queue.
		</synopsis>
		<syntax>
			<parameter name="queuename" required="true" />
			<parameter name="option" required="true">
				<enumlist>
					<enum name="logged">
						<para>Returns the number of logged-in members for the specified queue.</para>
					</enum>
					<enum name="free">
						<para>Returns the number of logged-in members for the specified queue that either can take calls or are currently wrapping up after a previous call.</para>
					</enum>
					<enum name="ready">
						<para>Returns the number of logged-in members for the specified queue that are immediately available to answer a call.</para>
					</enum>
					<enum name="count">
						<para>Returns the total number of members for the specified queue.</para>
					</enum>
					<enum name="penalty">
						<para>Gets or sets queue member penalty.</para>
					</enum>
					<enum name="paused">
						<para>Gets or sets queue member paused status.</para>
					</enum>
					<enum name="callinuse">
						<para>Gets or sets queue member callinuse.</para>
					</enum>
				</enumlist>
			</parameter>
			<parameter name="interface" required="false" />
		</syntax>
		<description>
			<para>Allows access to queue counts [R] and member information [R/W].</para>
			<para>
				<replaceable>queuename</replaceable> is required for all operations
				<replaceable>interface</replaceable> is required for all member operations.
			</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</function>
	<function name="QUEUE_EXISTS" language="en_US">
		<synopsis>
			Check if a named queue exists on this server
		</synopsis>
		<syntax>
			<parameter name="queuename" />
		</syntax>
		<description>
			<para>Returns 1 if the specified queue exists, 0 if it does not</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_MEMBER_COUNT</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</function>
	<function name="QUEUE_WAITING_COUNT" language="en_US">
		<synopsis>
			Count number of calls currently waiting in a queue.
		</synopsis>
		<syntax>
			<parameter name="queuename" />
		</syntax>
		<description>
			<para>Returns the number of callers currently waiting in the specified <replaceable>queuename</replaceable>.</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_MEMBER_COUNT</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</function>
	<function name="QUEUE_MEMBER_LIST" language="en_US">
		<synopsis>
			Returns a list of interfaces on a queue.
		</synopsis>
		<syntax>
			<parameter name="queuename" required="true" />
		</syntax>
		<description>
			<para>Returns a comma-separated list of members associated with the specified <replaceable>queuename</replaceable>.</para>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_MEMBER_COUNT</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</function>
	<function name="QUEUE_MEMBER_PENALTY" language="en_US">
		<synopsis>
			Gets or sets queue members penalty.
		</synopsis>
		<syntax>
			<parameter name="queuename" required="true" />
			<parameter name="interface" required="true" />
		</syntax>
		<description>
			<para>Gets or sets queue members penalty.</para>
			<warning><para>This function has been deprecated in favor of the <literal>QUEUE_MEMBER()</literal> function</para></warning>
		</description>
		<see-also>
			<ref type="application">Queue</ref>
			<ref type="application">QueueLog</ref>
			<ref type="application">AddQueueMember</ref>
			<ref type="application">RemoveQueueMember</ref>
			<ref type="application">PauseQueueMember</ref>
			<ref type="application">UnpauseQueueMember</ref>
			<ref type="function">QUEUE_VARIABLES</ref>
			<ref type="function">QUEUE_MEMBER</ref>
			<ref type="function">QUEUE_MEMBER_COUNT</ref>
			<ref type="function">QUEUE_EXISTS</ref>
			<ref type="function">QUEUE_WAITING_COUNT</ref>
			<ref type="function">QUEUE_MEMBER_LIST</ref>
			<ref type="function">QUEUE_MEMBER_PENALTY</ref>
		</see-also>
	</function>
	<manager name="Queues" language="en_US">
		<synopsis>
			Queues.
		</synopsis>
		<syntax>
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueStatus" language="en_US">
		<synopsis>
			Show queue status.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Queue" />
			<parameter name="Member" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueSummary" language="en_US">
		<synopsis>
			Show queue summary.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Queue" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueAdd" language="en_US">
		<synopsis>
			Add interface to queue.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Queue" required="true" />
			<parameter name="Interface" required="true" />
			<parameter name="Penalty" />
			<parameter name="Paused" />
			<parameter name="MemberName" />
			<parameter name="StateInterface" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueRemove" language="en_US">
		<synopsis>
			Remove interface from queue.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Queue" required="true" />
			<parameter name="Interface" required="true" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueuePause" language="en_US">
		<synopsis>
			Makes a queue member temporarily unavailable.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Interface" required="true" />
			<parameter name="Paused" required="true" />
			<parameter name="Queue" />
			<parameter name="Reason" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueLog" language="en_US">
		<synopsis>
			Adds custom entry in queue_log.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Queue" required="true" />
			<parameter name="Event" required="true" />
			<parameter name="Uniqueid" />
			<parameter name="Interface" />
			<parameter name="Message" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueuePenalty" language="en_US">
		<synopsis>
			Set the penalty for a queue member.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Interface" required="true" />
			<parameter name="Penalty" required="true" />
			<parameter name="Queue" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueRule" language="en_US">
		<synopsis>
			Queue Rules.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Rule" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueReload" language="en_US">
		<synopsis>
			Reload a queue, queues, or any sub-section of a queue or queues.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Queue" />
			<parameter name="Members">
				<enumlist>
					<enum name="yes" />
					<enum name="no" />
				</enumlist>
			</parameter>
			<parameter name="Rules">
				<enumlist>
					<enum name="yes" />
					<enum name="no" />
				</enumlist>
			</parameter>
			<parameter name="Parameters">
				<enumlist>
					<enum name="yes" />
					<enum name="no" />
				</enumlist>
			</parameter>
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueReset" language="en_US">
		<synopsis>
			Reset queue statistics.
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Queue" />
		</syntax>
		<description>
		</description>
	</manager>
	<manager name="QueueCallInuse" language="en_US">
		<synopsis>
			Set interface to allow multiple calls
		</synopsis>
		<syntax>
			<xi:include xpointer="xpointer(/docs/manager[@name='Login']/syntax/parameter[@name='ActionID'])" />
			<parameter name="Interface" required="true" />
			<parameter name="CallInuse" required="true" />
			<parameter name="Queue" required="true" />
		</syntax>
		<description>
		</description>
	</manager>
 ***/

enum {
	QUEUE_STRATEGY_RINGALL = 0,
	QUEUE_STRATEGY_LEASTRECENT,
	QUEUE_STRATEGY_FEWESTCALLS,
	QUEUE_STRATEGY_RANDOM,
	QUEUE_STRATEGY_RRMEMORY,
	QUEUE_STRATEGY_LINEAR,
	QUEUE_STRATEGY_WRANDOM,
	QUEUE_STRATEGY_RRORDERED,
};

enum {
     QUEUE_AUTOPAUSE_OFF = 0,
     QUEUE_AUTOPAUSE_ON,
     QUEUE_AUTOPAUSE_ALL
};

enum queue_reload_mask {
	QUEUE_RELOAD_PARAMETERS = (1 << 0),
	QUEUE_RELOAD_MEMBER = (1 << 1),
	QUEUE_RELOAD_RULES = (1 << 2),
	QUEUE_RESET_STATS = (1 << 3),
	QUEUE_RELOAD_REALTIME = (1 << 4),
};

enum member_type {
	QUEUE_ADD_MEMBER_STATIC = (1 << 0),
	QUEUE_ADD_MEMBER_REALTIME = (1 << 1),
	QUEUE_ADD_MEMBER_DYNAMIC = (1 << 2),
};

static const struct strategy {
	int strategy;
	const char *name;
} strategies[] = {
	{ QUEUE_STRATEGY_RINGALL, "ringall" },
	{ QUEUE_STRATEGY_LEASTRECENT, "leastrecent" },
	{ QUEUE_STRATEGY_FEWESTCALLS, "fewestcalls" },
	{ QUEUE_STRATEGY_RANDOM, "random" },
	{ QUEUE_STRATEGY_RRMEMORY, "rrmemory" },
	{ QUEUE_STRATEGY_RRMEMORY, "roundrobin" },
	{ QUEUE_STRATEGY_LINEAR, "linear" },
	{ QUEUE_STRATEGY_WRANDOM, "wrandom"},
	{ QUEUE_STRATEGY_RRORDERED, "rrordered"},
};

static const struct autopause {
	int autopause;
	const char *name;
} autopausesmodes [] = {
	{ QUEUE_AUTOPAUSE_OFF,"no" },
	{ QUEUE_AUTOPAUSE_ON, "yes" },
	{ QUEUE_AUTOPAUSE_ALL,"all" },
};


static struct ast_taskprocessor *devicestate_tps;

#define DEFAULT_RETRY		5
#define DEFAULT_TIMEOUT		15
#define RECHECK			1		/*!< Recheck every second to see we we're at the top yet */
#define MAX_PERIODIC_ANNOUNCEMENTS 10           /*!< The maximum periodic announcements we can have */
#define DEFAULT_MIN_ANNOUNCE_FREQUENCY 15       /*!< The minimum number of seconds between position announcements \
                                                     The default value of 15 provides backwards compatibility */
#define MAX_QUEUE_BUCKETS 53

enum member_result {
	RES_OKAY = 0,			/*!< Action completed */
	RES_EXISTS = -1,		/*!< Entry already exists */
	RES_OUTOFMEMORY	= -2,		/*!< Out of memory */
	RES_NOSUCHQUEUE	= -3,		/*!< No such queue */
	RES_NOT_DYNAMIC = -4,		/*!< Member is not dynamic */
	RES_ERROR = -5,			/*!< Member is mis configured */
};

static char *app = "Queue";
static char *app_aqm = "AddQueueMember" ;
static char *app_rqm = "RemoveQueueMember" ;
static char *app_pqm = "PauseQueueMember" ;
static char *app_upqm = "UnpauseQueueMember" ;
static char *app_ql = "QueueLog" ;

/*! \brief Persistent Members astdb family */
static const char * const pm_family = "Queue/PersistentMembers";
/* The maximum length of each persistent member queue database entry */
#define PM_MAX_LEN 8192

/*! \brief queues.conf [general] option */
static int queue_persistent_members = 0;

/*! \brief queues.conf per-queue weight option */
static int use_weight = 0;

/*! \brief queues.conf [general] option */
static int autofill_default = 1;

/*! \brief queues.conf [general] option */
static int montype_default = 0;

/*! \brief queues.conf [general] option */
static int shared_lastcall = 1;

/*! \brief Subscription to device state change events */
static struct ast_event_sub *device_state_sub;

/*! \brief queues.conf [general] option */
static int update_cdr = 0;

/*! \brief queues.conf [general] option */
static int negative_penalty_invalid = 0;

/*! \brief queues.conf [general] option */
static int log_membername_as_agent = 0;

enum queue_result {
	QUEUE_UNKNOWN = 0,
	QUEUE_TIMEOUT = 1,
	QUEUE_JOINEMPTY = 2,
	QUEUE_LEAVEEMPTY = 3,
	QUEUE_JOINUNAVAIL = 4,
	QUEUE_LEAVEUNAVAIL = 5,
	QUEUE_FULL = 6,
	QUEUE_CONTINUE = 7,
};

static const struct {
	enum queue_result id;
	char *text;
} queue_results[] = {
	{ QUEUE_UNKNOWN, "UNKNOWN" },
	{ QUEUE_TIMEOUT, "TIMEOUT" },
	{ QUEUE_JOINEMPTY,"JOINEMPTY" },
	{ QUEUE_LEAVEEMPTY, "LEAVEEMPTY" },
	{ QUEUE_JOINUNAVAIL, "JOINUNAVAIL" },
	{ QUEUE_LEAVEUNAVAIL, "LEAVEUNAVAIL" },
	{ QUEUE_FULL, "FULL" },
	{ QUEUE_CONTINUE, "CONTINUE" },
};

enum queue_timeout_priority {
	TIMEOUT_PRIORITY_APP,
	TIMEOUT_PRIORITY_CONF,
};

/*! \brief We define a custom "local user" structure because we
 *  use it not only for keeping track of what is in use but
 *  also for keeping track of who we're dialing.
 *
*/

struct callattempt {
	struct ast_channel *chan;                  /*! Channel called */
	int metric;                                /*! Metric calculated according to strategy */
	struct member *member;                     /*! Member assosiated with this attempt */
	struct ast_party_connected_line connected; /*! Saved connected party info from an AST_CONTROL_CONNECTED_LINE. */
	unsigned int stillgoing:1;                 /*! This attempt is valid and active */
	unsigned int reserved:1;                   /*! Is this attempt been attempted*/
	unsigned int active:1;                     /*! Is this attempt active in a call*/
	unsigned int pending_connected_update:1;   /*! TRUE if caller id is not available for connected line*/
	unsigned int dial_callerid_absent:1;       /*! TRUE if caller id is not available for connected line */
	unsigned int watching:1;                   /*! TRUE if callattempt is been watched */
	struct ast_aoc_decoded *aoc_s_rate_list;
};

struct queue_ent {
	struct call_queue *parent;             /*!< What queue is our parent */
	char digits[AST_MAX_EXTENSION];        /*!< Digits entered while in queue */
	int valid_digits;                      /*!< Digits entered correspond to valid extension. Exited */
	int pos;                               /*!< Where we are in the queue */
	int prio;                              /*!< Our priority */
	int last_pos_said;                     /*!< Last position we told the user */
	int ring_when_ringing;                 /*!< Should we only use ring indication when a channel is ringing? */
	struct timeval last_pannounce_time;    /*!< The last time we played a periodic announcement */
	int last_periodic_announce_sound;      /*!< The last periodic announcement we made */
	struct timeval last_pos;               /*!< Last time we told the user their position */
	int opos;                              /*!< Where we started in the queue */
	int handled;                           /*!< Whether our call was handled */
	int pending;                           /*!< Non-zero if we are attempting to call a member */
	int max_penalty;                       /*!< Limit the members that can take this call to this penalty or lower */
	int min_penalty;                       /*!< Limit the members that can take this call to this penalty or higher */
	int linpos;                            /*!< If using linear strategy, what position are we at? */
	int linwrapped;                        /*!< Is the linpos wrapped? */
	struct timeval start;                  /*!< When we started holding */
	struct timeval expire;                 /*!< When this entry should expire (time out of queue) */
	int cancel_answered_elsewhere;	       /*!< Whether we should force the CAE flag on this call (C) option*/
	struct ao2_container *attempts;        /*!< Container holding all call attempts*/
	struct ast_channel *chan;              /*!< Our channel */
	struct rule_list *rules;               /*!< Pointer holding the ref for the queue penalty rules */
	struct penalty_rule *pr;               /*!< Active penalty rule */
	AST_LIST_ENTRY(queue_ent) next;        /*!< The next queue entry */
};

/*! \brief keep track of device state changes */
struct mem_state {
	char state_interface[80];              /*!< Technology/Location from which to read devicestate changes */
	int reserved;                          /*!< This interface is reserved for pending call */
	int active;                            /*!< This interface is active on a call */
	int status;                            /*!< Status of queue member */
};

struct member {
	AST_DECLARE_STRING_FIELDS(
		AST_STRING_FIELD(interface);   /*!< Technology/Location to dial to reach this member*/
		AST_STRING_FIELD(membername);  /*!< Member name to use in queue logs */
		AST_STRING_FIELD(rt_uniqueid); /*!< Unique id of realtime member entry */
	);
	int penalty;                           /*!< Are we a last resort? */
	int calls;                             /*!< Number of calls serviced by this member */
	struct timeval lastcall;               /*!< When last successful call was hungup */
	int lastwrapup;                        /*!< Last wrapuptime */
	unsigned int dynamic:1;                /*!< Is this member dynamic? */
	unsigned int realtime:1;               /*!< Is this member realtime? */
	unsigned int paused:1;                 /*!< Are we paused (not accepting calls)? */
	unsigned int dead:1;                   /*!< Used to detect members deleted in realtime */
	unsigned int callinuse:1;              /*!< Are we dynamically added? */
	struct mem_state *device;              /*!< Device information */
};

enum empty_conditions {
	QUEUE_EMPTY_PENALTY = (1 << 0),
	QUEUE_EMPTY_PAUSED = (1 << 1),
	QUEUE_EMPTY_INUSE = (1 << 2),
	QUEUE_EMPTY_RINGING = (1 << 3),
	QUEUE_EMPTY_UNAVAILABLE = (1 << 4),
	QUEUE_EMPTY_INVALID = (1 << 5),
	QUEUE_EMPTY_UNKNOWN = (1 << 6),
	QUEUE_EMPTY_WRAPUP = (1 << 7),
};

/* values used in multi-bit flags in call_queue */
#define ANNOUNCEHOLDTIME_ALWAYS 1
#define ANNOUNCEHOLDTIME_ONCE 2
#define QUEUE_EVENT_VARIABLES 3

struct penalty_rule {
	int time;                           /*!< Number of seconds that need to pass before applying this rule */
	int max_value;                      /*!< The amount specified in the penalty rule for max penalty */
	int min_value;                      /*!< The amount specified in the penalty rule for min penalty */
	int max_relative;                   /*!< Is the max adjustment relative? 1 for relative, 0 for absolute */
	int min_relative;                   /*!< Is the min adjustment relative? 1 for relative, 0 for absolute */
	AST_LIST_ENTRY(penalty_rule) list;  /*!< Next penalty_rule */
};

#define ANNOUNCEPOSITION_YES 1 /*!< We announce position */
#define ANNOUNCEPOSITION_NO 2 /*!< We don't announce position */
#define ANNOUNCEPOSITION_MORE_THAN 3 /*!< We say "Currently there are more than <limit>" */
#define ANNOUNCEPOSITION_LIMIT 4 /*!< We not announce position more than <limit> */

struct call_queue {
	AST_DECLARE_STRING_FIELDS(
		/*! Queue name */
		AST_STRING_FIELD(name);
		/*! Music on Hold class */
		AST_STRING_FIELD(moh);
		/*! Announcement to play when call is answered */
		AST_STRING_FIELD(announce);
		/*! Exit context */
		AST_STRING_FIELD(context);
		/*! Macro to run upon member connection */
		AST_STRING_FIELD(membermacro);
		/*! Gosub to run upon member connection */
		AST_STRING_FIELD(membergosub);
		/*! Default rule to use if none specified in call to Queue() */
		AST_STRING_FIELD(defaultrule);
		/*! Sound file: "Your call is now first in line" (def. queue-youarenext) */
		AST_STRING_FIELD(sound_next);
		/*! Sound file: "There are currently" (def. queue-thereare) */
		AST_STRING_FIELD(sound_thereare);
		/*! Sound file: "calls waiting to speak to a representative." (def. queue-callswaiting) */
		AST_STRING_FIELD(sound_calls);
		/*! Sound file: "Currently there are more than" (def. queue-quantity1) */
		AST_STRING_FIELD(queue_quantity1);
		/*! Sound file: "callers waiting to speak with a representative" (def. queue-quantity2) */
		AST_STRING_FIELD(queue_quantity2);
		/*! Sound file: "The current estimated total holdtime is" (def. queue-holdtime) */
		AST_STRING_FIELD(sound_holdtime);
		/*! Sound file: "minutes." (def. queue-minutes) */
		AST_STRING_FIELD(sound_minutes);
		/*! Sound file: "minute." (def. queue-minute) */
		AST_STRING_FIELD(sound_minute);
		/*! Sound file: "seconds." (def. queue-seconds) */
		AST_STRING_FIELD(sound_seconds);
		/*! Sound file: "Thank you for your patience." (def. queue-thankyou) */
		AST_STRING_FIELD(sound_thanks);
		/*! Sound file: Custom announce for caller, no default */
		AST_STRING_FIELD(sound_callerannounce);
		/*! Sound file: "Hold time" (def. queue-reporthold) */
		AST_STRING_FIELD(sound_reporthold);
	);
	/*! Sound files: Custom announce, no default */
	struct ast_str *sound_periodicannounce[MAX_PERIODIC_ANNOUNCEMENTS];
	unsigned int dead:1;
	unsigned int eventwhencalled:2;
	unsigned int ringinuse:1;
	unsigned int setinterfacevar:1;
	unsigned int setqueuevar:1;
	unsigned int setqueueentryvar:1;
	unsigned int reportholdtime:1;
	unsigned int timeoutrestart:1;
	unsigned int announceholdtime:2;
	unsigned int announceposition:3;
	int strategy:4;
	unsigned int maskmemberstatus:1;
	unsigned int realtime:1;
	unsigned int relativeperiodicannounce:1;
	unsigned int autopausebusy:1;
	unsigned int autopauseunavail:1;
	enum empty_conditions joinempty;
	enum empty_conditions leavewhenempty;
	int announcepositionlimit;          /*!< How many positions we announce? */
	int announcefrequency;              /*!< How often to announce their position */
	int minannouncefrequency;           /*!< The minimum number of seconds between position announcements (def. 15) */
	int periodicannouncefrequency;      /*!< How often to play periodic announcement */
	int numperiodicannounce;            /*!< The number of periodic announcements configured */
	int randomperiodicannounce;         /*!< Are periodic announcments randomly chosen */
	int roundingseconds;                /*!< How many seconds do we round to? */
	int servicelevel;                   /*!< seconds setting for servicelevel*/
	char monfmt[8];                     /*!< Format to use when recording calls */
	int montype;                        /*!< Monitor type  Monitor vs. MixMonitor */
	int maxlen;                         /*!< Max number of entries */
	int wrapuptime;                     /*!< Wrapup Time */
	int penaltymemberslimit;            /*!< Disregard penalty when queue has fewer than this many members */
	int retry;                          /*!< Retry calling everyone after this amount of time */
	int timeout;                        /*!< How long to wait for an answer */
	int weight;                         /*!< Respective weight */
	int autopause;                      /*!< Auto pause queue members if they fail to answer */
	int autopausedelay;                 /*!< Delay auto pause for autopausedelay seconds since last call */
	int timeoutpriority;                /*!< Do we allow a fraction of the timeout to occur for a ring? */
	/* Queue strategy things */
	int memberdelay;                    /*!< Seconds to delay connecting member to caller */
	int autofill;                       /*!< Ignore the head call status and ring an available agent */
	struct timeval reload;              /*!< Time the queue will be reloaded from RT */
	struct queue_data *data;            /*!< Queue statistics */
};

struct queue_data {
	int qhash;                          /*!< Hash for queue */
	unsigned int wrapped:1;
	int count;                          /*!< How many entries */
	int holdtime;                       /*!< Current avg holdtime, based on an exponential average */
	int talktime;                       /*!< Current avg talktime, based on the same exponential average */
	int callscompleted;                 /*!< Number of queue calls completed */
	int callsabandoned;                 /*!< Number of queue calls abandoned */
	int callscompletedinsl;             /*!< Number of calls answered with servicelevel*/
	int rrpos;                          /*!< Round Robin - position */
	AST_LIST_HEAD(, queue_ent)  *head;  /*!< Head of the list of callers */
	struct ao2_container *members;      /*!< Head of the list of members */
};

struct rule_list {
	char name[80];
	struct ao2_container *rules;
};

static struct ao2_container *queues;
static struct ao2_container *devices;
static struct ao2_container *rules;
static struct ao2_container *qdata;

static int do_set_member_penalty_paused(struct call_queue *q, struct member *mem, int pause, int value, const char *reason);
static void pm_load_member_config(struct call_queue *q);
static char *queue_refshow(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a);
static struct member *interface_exists(struct call_queue *q, const char *interface);
static int set_member_paused(const char *queuename, const char *interface, const char *reason, int paused);
static void queue_transfer_fixup(void *data, struct ast_channel *old_chan, struct ast_channel *new_chan);

/*! \brief sets the QUEUESTATUS channel variable */
static void set_queue_result(struct ast_channel *chan, enum queue_result res)
{
	int i;

	for (i = 0; i < ARRAY_LEN(queue_results); i++) {
		if (queue_results[i].id == res) {
			pbx_builtin_setvar_helper(chan, "QUEUESTATUS", queue_results[i].text);
			return;
		}
	}
}

/*! \brief return strategy name from strategy*/
static const char *int2strat(int strategy)
{
	int x;

	for (x = 0; x < ARRAY_LEN(strategies); x++) {
		if (strategy == strategies[x].strategy)
			return strategies[x].name;
	}

	return "<unknown>";
}

/*! brief return strategy from strategy name*/
static int strat2int(const char *strategy)
{
	int x;

	for (x = 0; x < ARRAY_LEN(strategies); x++) {
		if (!strcasecmp(strategy, strategies[x].name))
			return strategies[x].strategy;
	}

	return -1;
}

/*! brief return a autopause setting from name*/
static int autopause2int(const char *autopause)
{
	int x;
	/*This 'double check' that default value is OFF */
	if (ast_strlen_zero(autopause))
		return QUEUE_AUTOPAUSE_OFF;

	/*This 'double check' is to ensure old values works */
	if(ast_true(autopause))
		return QUEUE_AUTOPAUSE_ON;

	for (x = 0; x < ARRAY_LEN(autopausesmodes); x++) {
		if (!strcasecmp(autopause, autopausesmodes[x].name))
			return autopausesmodes[x].autopause;
	}

	/*This 'double check' that default value is OFF */
	return QUEUE_AUTOPAUSE_OFF;
}

/*!
 * \brief ao2 callback to calculate hash of a queue by name
 */
static int queue_hash_cb(const void *obj, const int flags)
{
	const struct call_queue *q = obj;
	const char *name = q->name;

	return ast_str_case_hash(name);
}


/*!
 * \brief ao2 callback to find queue by name
 * \note this is the default function used by ao2_find
 */
static int queue_cmp_cb(void *obj, void *arg, int flags)
{
	const struct call_queue *q = obj, *q2 = arg;
	const char *name = (arg && (flags & OBJ_POINTER)) ? q2->name : arg;

	if (!ast_strlen_zero(name) && !strcasecmp(q->name, name)) {
		return CMP_MATCH | CMP_STOP;
	} else {
		return 0;
	}
}

/*!
 * \brief ao2 callback to calculate hash of a queue by name
 */
static int qdata_hash_cb(const void *obj, const int flags)
{
	const struct queue_data *d = obj;
	int qhash = d->qhash;

	return qhash;
}


/*!
 * \brief ao2 callback to find queue by name
 * \note this is the default function used by ao2_find
 */
static int qdata_cmp_cb(void *obj, void *arg, int flags)
{
	const struct queue_data *d = obj, *d2 = arg;
	const char *name = arg;
	int nhash = (ast_strlen_zero(name)) ? 0 : ast_str_case_hash(name);
	int qhash = (arg && (flags & OBJ_POINTER)) ? d2->qhash : nhash;

	if (qhash && (d->qhash == qhash)) {
		return CMP_MATCH | CMP_STOP;
	} else {
		return 0;
	}
}

/*! \brief Set channel variables of queue */
static void set_queue_variables(struct call_queue *q, struct ast_channel *chan)
{
	char interfacevar[256]="";
	float sl = 0;
	struct queue_data *data = q->data;

	if (q->setqueuevar) {
		sl = 0;
		ao2_lock(data);
		if (data->callscompleted > 0) {
			sl = 100 * ((float) data->callscompletedinsl / (float) data->callscompleted);
		}

		snprintf(interfacevar, sizeof(interfacevar),
			"QUEUENAME=%s,QUEUEMAX=%d,QUEUESTRATEGY=%s,QUEUECALLS=%d,QUEUEHOLDTIME=%d,QUEUETALKTIME=%d,QUEUECOMPLETED=%d,QUEUEABANDONED=%d,QUEUESRVLEVEL=%d,QUEUESRVLEVELPERF=%2.1f",
			q->name, q->maxlen, int2strat(q->strategy), data->count, data->holdtime, data->talktime,
			data->callscompleted, data->callsabandoned,  q->servicelevel, sl);

		pbx_builtin_setvar_multiple(chan, interfacevar);
		ao2_unlock(data);
	}
}

/*! \brief Insert the 'new' callattempt entry after the 'prev' entry of queue 'q' */
static inline void insert_entry(struct queue_ent *new, int *pos)
{
	new->pos = ++(*pos);
	new->opos = *pos;
	ao2_lock(new->parent->data);
	new->parent->data->count++;
	ao2_unlock(new->parent->data);
}

/*! \brief return the device state for a member*/
static int get_device_status(struct member *m)
{
	int ret;
	struct mem_state *s = m->device;

	ao2_lock(s);

	ret = s->status;
	switch (s->status) {
		case AST_DEVICE_INVALID:
		case AST_DEVICE_UNAVAILABLE:
		case AST_DEVICE_BUSY:
			break;
		case AST_DEVICE_INUSE:
		case AST_DEVICE_RINGING:
		case AST_DEVICE_RINGINUSE:
		case AST_DEVICE_ONHOLD:
			/* if im active and may not place calls when INUSE im actually BUSY */
			if ((s->reserved || s->active) && !m->callinuse) {
				ret = AST_DEVICE_BUSY;
			}
			break;
		case AST_DEVICE_NOT_INUSE:
		case AST_DEVICE_UNKNOWN:
			/* it seems that i have this device active but the system does not */
			if (s->active) {
				ret = (m->callinuse) ? AST_DEVICE_INUSE : AST_DEVICE_BUSY;
			} else if (s->reserved) {
				ret = (m->callinuse) ? AST_DEVICE_RINGING : AST_DEVICE_BUSY;
			}
	}
        ao2_unlock(s);

        return ret;
}

/*! \brief Check if members are available
 *
 * This function checks to see if members are available to be called. If any member
 * is available, the function immediately returns 0. If no members are available,
 * then -1 is returned.
 */
static int get_member_status(const struct queue_ent *qe, int join)
{
	struct member *member;
	struct ao2_iterator mem_iter;
	struct call_queue *q = qe->parent;
	enum empty_conditions conditions;

	conditions = (join) ? q->joinempty : q->leavewhenempty;

	if (!conditions) {
		return 0;
	}

	mem_iter = ao2_iterator_init(q->data->members, 0);
	while((member = ao2_iterator_next(&mem_iter))) {
		ao2_lock(member);
		if ((qe->max_penalty && (member->penalty > qe->max_penalty)) || (qe->min_penalty && (member->penalty < qe->min_penalty))) {
			if (conditions & QUEUE_EMPTY_PENALTY) {
				ast_debug(4, "%s is unavailable because his penalty is not between %d and %d\n", member->membername, qe->min_penalty, qe->max_penalty);
				ao2_unlock(member);
				ao2_ref(member, -1);
				continue;
			}
		}

		switch (get_device_status(member)) {
		case AST_DEVICE_INVALID:
			if (conditions & QUEUE_EMPTY_INVALID) {
				ast_debug(4, "%s is unavailable because his device state is 'invalid'\n", member->membername);
				break;
			}
			goto default_case;
		case AST_DEVICE_UNAVAILABLE:
			if (conditions & QUEUE_EMPTY_UNAVAILABLE) {
				ast_debug(4, "%s is unavailable because his device state is 'unavailable'\n", member->membername);
				break;
			}
			goto default_case;
		case AST_DEVICE_INUSE:
		case AST_DEVICE_BUSY:
			if (conditions & QUEUE_EMPTY_INUSE) {
				ast_debug(4, "%s is unavailable because his device state is 'inuse'\n", member->membername);
				break;
			}
			goto default_case;
		case AST_DEVICE_RINGING:
			if (conditions & QUEUE_EMPTY_RINGING) {
				ast_debug(4, "%s is unavailable because his device state is 'ringing'\n", member->membername);
				break;
			}
			goto default_case;
		case AST_DEVICE_UNKNOWN:
			if (conditions & QUEUE_EMPTY_UNKNOWN) {
				ast_debug(4, "%s is unavailable because his device state is 'unknown'\n", member->membername);
				break;
			}
			/* Fall-through */
		default:
		default_case:
			if (member->paused && (conditions & QUEUE_EMPTY_PAUSED)) {
				ast_debug(4, "%s is unavailable because he is paused'\n", member->membername);
				break;
			} else if ((conditions & QUEUE_EMPTY_WRAPUP) && !ast_tvzero(member->lastcall) && member->lastwrapup && (ast_tvdiff_sec(ast_tvnow(), member->lastcall) <= member->lastwrapup)) {
				ast_debug(4, "%s is unavailable because it has only been %d seconds since his last call (wrapup time is %d)\n", member->membername, (int)ast_tvdiff_sec(ast_tvnow(), member->lastcall), member->lastwrapup);
				break;
			} else {
				ast_debug(4, "%s is available.\n", member->membername);
				ao2_unlock(member);
				ao2_ref(member, -1);
				ao2_iterator_destroy(&mem_iter);
				return 0;
			}
			break;
		}
		ao2_unlock(member);
		ao2_ref(member, -1);
	}
	ao2_iterator_destroy(&mem_iter);
	return -1;
}

/*! \brief Un ref a device if im the last consumer unlink it*/
static void unref_device(struct mem_state *s) {
	if (!s) {
		return;
	}

	ao2_lock(devices);
	/* remove our ref*/
	if (ao2_ref(s, -1) == 2) {
		/* we were the only consumer unlink*/
		ao2_find(devices, s, OBJ_UNLINK | OBJ_POINTER | OBJ_NODATA | OBJ_NOLOCK);
	}
	ao2_unlock(devices);
}

/*! \brief send a QueueMemberStatus manager_event when device state changes*/
static int update_status(void *data)
{
	struct ao2_iterator qiter;
	struct ao2_iterator miter;
	struct call_queue *q;
	struct member *m;
	struct mem_state *s = data;

	qiter = ao2_iterator_init(queues, 0);
	while ((q = ao2_iterator_next(&qiter))) {
		if (q->maskmemberstatus) {
			ao2_ref(q, -1);
			continue;
		}
		miter = ao2_iterator_init(q->data->members, 0);
		while((m = ao2_iterator_next(&miter))) {
			ao2_lock(m);
			if (m->device != s) {
				ao2_unlock(m);
				ao2_ref(m, -1);
				continue;
			}
			ao2_lock(s);
			manager_event(EVENT_FLAG_AGENT, "QueueMemberStatus",
				"Queue: %s\r\n"
				"Location: %s\r\n"
				"MemberName: %s\r\n"
				"StateInterface: %s\r\n"
				"Membership: %s\r\n"
				"Penalty: %d\r\n"
				"CallsTaken: %d\r\n"
				"LastCall: %d\r\n"
				"Status: %d\r\n"
				"Paused: %d\r\n"
				"CallInuse: %d\r\n",
				q->name, m->interface, m->membername, s->state_interface, m->dynamic ? "dynamic" : m->realtime ? "realtime" : "static",
				m->penalty, m->calls, (int)m->lastcall.tv_sec, s->status, m->paused, m->callinuse
			);
			ao2_unlock(s);
			ao2_unlock(m);
			ao2_ref(m, -1);
		}
		ao2_iterator_destroy(&miter);
		ao2_ref(q, -1);
	}
	ao2_iterator_destroy(&qiter);

	unref_device(s);

	return 0;
}

/*! \brief set the device state of a member explicitly
 *  \note a change update manager event will be sent
 */
static int set_device_status(const char *device, int status)
{
	struct mem_state *s;

	if (!(s = ao2_find(devices, (char *)device, 0))) {
		return -1;
	}

	ao2_lock(s);
	if (s->status != status) {
		s->status = status;
		ao2_unlock(s);
		if (ast_taskprocessor_push(devicestate_tps, update_status, s)) {
			unref_device(s);
		}
	} else {
		ao2_unlock(s);
		unref_device(s);
	}

	return 0;
}

/*! \brief callback used when device state changes*/
static void device_state_cb(const struct ast_event *event, void *unused)
{
	enum ast_device_state state;
	const char *device;

	state = ast_event_get_ie_uint(event, AST_EVENT_IE_STATE);
	device = ast_event_get_ie_str(event, AST_EVENT_IE_DEVICE);

	if (ast_strlen_zero(device)) {
		ast_log(LOG_ERROR, "Received invalid event that had no device IE\n");
		return;
	}

	if (set_device_status(device, state)) {
		ast_debug(1, "Device '%s' changed to state '%d' (%s)\n", device, state, ast_devstate2str(state));
	} else {
		ast_debug(3, "Device '%s' changed to state '%d' (%s) but we don't care because they're not a member of any queue.\n", device, state, ast_devstate2str(state));
	}
}

/*! \brief Helper function which converts from extension state to device state values */
static int extensionstate2devicestate(int state)
{
	switch (state) {
	case AST_EXTENSION_NOT_INUSE:
		state = AST_DEVICE_NOT_INUSE;
		break;
	case AST_EXTENSION_INUSE:
		state = AST_DEVICE_INUSE;
		break;
	case AST_EXTENSION_BUSY:
		state = AST_DEVICE_BUSY;
		break;
	case AST_EXTENSION_RINGING:
		state = AST_DEVICE_RINGING;
		break;
	case AST_EXTENSION_ONHOLD:
		state = AST_DEVICE_ONHOLD;
		break;
	case AST_EXTENSION_UNAVAILABLE:
		state = AST_DEVICE_UNAVAILABLE;
		break;
	case AST_EXTENSION_REMOVED:
	case AST_EXTENSION_DEACTIVATED:
	default:
		state = AST_DEVICE_INVALID;
		break;
	}

	return state;
}

/*! \brief callback called when a extension hint is notified of change*/
static int extension_state_cb(const char *context, const char *exten, enum ast_extension_states state, void *data)
{
	char *device;
	int status = extensionstate2devicestate(state);

	if (!asprintf(&device, "hint:%s@%s", exten, context)) {
		ast_log(LOG_WARNING, "asprintf() failed: %s\n", strerror(errno));
		return 0;
	}

	if (set_device_status(device, status)) {
		ast_debug(1, "Extension '%s@%s' changed to state '%d' (%s)\n", exten, context, status, ast_devstate2str(status));
	} else {
		ast_debug(3, "Extension '%s@%s' changed state but we don't care because they're not a member of any queue.\n",
			  exten, context);
	}

	return 0;
}

/* \brief find or create a member device state object*/
static struct mem_state *create_member_state(const char *state_interface) {
	struct mem_state *state;
	char *exten;
	char *context;
	char *device;

	/* ref will be held for each shared member and one ref for container */
	if ((state = ao2_find(devices, (char *)state_interface, 0))) {
		return state;
	} else  if (!(state = ao2_alloc(sizeof(*state), NULL))) {
		return NULL;
	}

	state->reserved = 0;
	if (!strncasecmp(state_interface, "hint:", 5)) {
		context = ast_strdupa(state_interface);
		exten = strsep(&context, "@") + 5;
		if (context) {
			ast_copy_string(state->state_interface, state_interface, sizeof(state->state_interface));
		} else {
			if (!asprintf(&device, "%s@default", state_interface)) {
				ast_log(AST_LOG_ERROR, "Failed to use state_interface %s@default\n", state_interface);
				ao2_ref(state, -1);
				return NULL;
			}
			ast_copy_string(state->state_interface, device, sizeof(state->state_interface));
		}
		state->status = extensionstate2devicestate(ast_extension_state(NULL, S_OR(context, "default"), exten));
	} else {
		ast_copy_string(state->state_interface, state_interface, sizeof(state->state_interface));
		state->status = ast_device_state(state->state_interface);
	}
	ao2_link(devices, state);

	return state;
}

/*! \brief Set current state of member querying channel driver or hint state*/
static int set_queue_member_status(struct member *m)
{
	int status;
	struct mem_state *s;

	ao2_lock(m);
	s = m->device;

	if (!strncasecmp(s->state_interface, "hint:", 5)) {
		char *context = ast_strdupa(s->state_interface);
		char *exten = strsep(&context, "@") + 5;
		status = extensionstate2devicestate(ast_extension_state(NULL, S_OR(context, "default"), exten));
	} else {
		status = ast_device_state(s->state_interface);
	}

	ao2_lock(s);
	if (s->status != status) {
		s->status = status;
		/* we must pass a ref to the task processor*/
		if (!ast_taskprocessor_push(devicestate_tps, update_status, s)) {
			ao2_ref(s, 1);
		}
	}
	ao2_unlock(s);
	ao2_unlock(m);

	return status;
}

/*!
 * \brief ao2 callback to calculate hash of a member by interface
 */
static int member_hash_fn(const void *obj, const int flags)
{
	const struct member *mem = obj;
	const char *interface = mem->interface;

	return ast_str_case_hash(interface);
}

/*!
 * \brief ao2 callback to find member by interface
 * \note this is the default function used by ao2_find
 */
static int member_cmp_fn(void *obj1, void *obj2, int flags)
{
	const struct member *mem1 = obj1;
	const struct member *mem2 = obj2;
	const char *iface = (obj2 && (flags & OBJ_POINTER)) ? mem2->interface : obj2;

	if (!ast_strlen_zero(iface) && !strcasecmp(mem1->interface, iface)) {
		return CMP_MATCH | CMP_STOP;
	} else {
		return 0;
	}
}

/*!
 * \brief ao2 callback to find a realtime member by uniqueid
 */
static int member_cmp_uniqueid_fn(void *obj1, void *arg, int flags)
{
	const struct member *mem1 = obj1;
	const struct member *mem2 = arg;
	const char *uniqueid = (arg && (flags & OBJ_POINTER)) ? mem2->rt_uniqueid : arg;

	if (mem1->realtime && !mem1->dead && !ast_strlen_zero(uniqueid) &&
	    !strcasecmp(mem1->rt_uniqueid, uniqueid)) {
		return CMP_MATCH | CMP_STOP;
	}

	return 0;
}

/*!
 * \brief ao2 callback to mark realtime members dead
 */
static int mark_realtime_member_dead(void *obj, void *arg, int flags)
{
	struct member *member = obj;

	if (member->realtime) {
		member->dead = 1;
		return CMP_MATCH;
	}
	return 0;
}

/*!
 * \brief ao2 callback to delete realtime members marked dead
 */
static int kill_realtime_dead_members(void *obj, void *arg, void *data, int flags)
{
	struct member *m = obj;
	const struct call_queue *q = data;

	if (m->realtime && m->dead) {
		if (!log_membername_as_agent) {
			ast_queue_log(q->name, "REALTIME", m->interface, "REMOVEMEMBER", "%s", "");
		} else {
			ao2_lock(m);
			ast_queue_log(q->name, "REALTIME", m->membername, "REMOVEMEMBER", "%s", "");
			ao2_unlock(m);
		}
		return CMP_MATCH;
	}
	return 0;
}

/*! \brief ao2 callback to reset member counters */
static int clear_queue_member_fn(void *obj1, void *arg, int flags)
{
	struct member *mem = obj1;

	ao2_lock(mem);
	mem->calls = 0;
	mem->lastwrapup = 0;
	mem->lastcall = ast_tv(0, 0);
	ao2_unlock(mem);

	return 0;
}

/*!
 * \brief ao2 callback to calculate hash of a device by state_interface
 */
static int device_hash_cb(const void *obj, const int flags)
{
	const struct mem_state *s = obj;
	const char *state_interface = s->state_interface;

	return ast_str_case_hash(state_interface);
}

/*!
 * \brief ao2 callback to find device by state_interface
 * \note this is the default function used by ao2_find
 */
static int device_cmp_cb(void *obj, void *arg, int flags)
{
	const struct mem_state *d = obj;
	const struct mem_state *d2 = arg;
	const char *iface = (arg && (flags & OBJ_POINTER)) ? d2->state_interface : arg;

	if (!ast_strlen_zero(iface) && !strcasecmp(d->state_interface, iface)) {
		return CMP_MATCH | CMP_STOP;
	} else {
		return 0;
	}
}

/*!
 * \brief ao2 callback to calculate hash of a rule by name
 */
static int rules_hash_cb(const void *obj, const int flags)
{
	const struct rule_list *rl = obj;
	const char *name = rl->name;

	return ast_str_case_hash(name);
}

/*!
 * \brief ao2 callback to calculate hash of a penalty rule by time
 */
static int penalty_hash_cb(const void *obj, const int flags)
{
	const struct penalty_rule *pr = obj;
	int time = pr->time;

	return time;
}

/*! \brief find the best penalty rule for duration */
static int get_best_rule_cb(void *obj, void *arg, void *data, int flags)
{
	int *time = arg;
	struct penalty_rule *cur = obj;
	struct penalty_rule **din = data, *best = *din;

	if ((cur->time >= *time) && (!best || (best && (cur->time < best->time)))) {
		if (best) {
			ao2_ref(best, -1);
		}
		ao2_ref(cur, 1);
		*din = cur;
		return CMP_MATCH;
	}
	return 0;
}

/*!
 * \brief ao2 callback to find rule by name
 * \note this is the default function used by ao2_find
 */
static int rules_cmp_cb(void *obj, void *arg, int flags)
{
	const struct rule_list *rl = obj;
	const struct rule_list *rl2 = arg;
	const char *name = (arg && (flags & OBJ_POINTER)) ? rl2->name : arg;

	if (!ast_strlen_zero(name) && !strcasecmp(rl->name, name)) {
		return CMP_MATCH | CMP_STOP;
	} else {
		return 0;
	}
}

/*!
 * \brief ao2 callback to calculate hash of a callattempt by member interface
 */
static int callattempt_hash_fn(const void *obj, const int flags)
{
	const struct callattempt *c = obj;
	const struct member *mem = c->member;
	const char *interface = mem->interface;

	return ast_str_case_hash(interface);
}

/*!
 * \brief ao2 callback to find callattempt been watched
 */
static int callattempt_watched_cb(void *obj, void *arg, const int flags)
{
	const struct callattempt *c = obj;
	const struct callattempt *c1 = arg;
	const struct member *mem = (arg) ? c1->member : NULL;
	const char *interface = (arg && (flags & OBJ_POINTER)) ? mem->interface : arg;

	if (!arg || ast_strlen_zero(interface) || !strcasecmp(interface, c->member->interface)) {
		return (c->stillgoing && c->chan) ? CMP_MATCH : 0;
	}
	return 0;
}

/*!
 * \brief ao2 callback to obtain the callattempt with best metric
 */
static int get_best_metric_cb(void *obj, void *arg, void *data, int flags)
{
	struct callattempt *cur = obj;
	struct callattempt **din = data, *best = *din;

	if (cur->stillgoing && !cur->chan &&
	    (!best || cur->metric < best->metric)) {
		if (best) {
			ao2_ref(best, -1);
		}
		ao2_ref(cur, 1);
		*din = cur;
		return CMP_MATCH;
	}
	return 0;
}

/*!
 * \brief Initialize Queue default values.
 * \note the queue's lock  must be held before executing this function
 */
static void init_queue(struct call_queue *q)
{
	int i;

	q->dead = 0;
	q->retry = DEFAULT_RETRY;
	q->timeout = DEFAULT_TIMEOUT;
	q->maxlen = 0;
	q->announcefrequency = 0;
	q->minannouncefrequency = DEFAULT_MIN_ANNOUNCE_FREQUENCY;
	q->announceholdtime = 1;
	q->announcepositionlimit = 10; /* Default 10 positions */
	q->announceposition = ANNOUNCEPOSITION_YES; /* Default yes */
	q->roundingseconds = 0; /* Default - don't announce seconds */
	q->servicelevel = 0;
	q->ringinuse = 1;
	q->setinterfacevar = 0;
	q->setqueuevar = 0;
	q->setqueueentryvar = 0;
	q->autofill = autofill_default;
	q->montype = montype_default;
	q->monfmt[0] = '\0';
	q->reportholdtime = 0;
	q->wrapuptime = 0;
	q->penaltymemberslimit = 0;
	q->joinempty = 0;
	q->leavewhenempty = 0;
	q->memberdelay = 0;
	q->maskmemberstatus = 0;
	q->eventwhencalled = 0;
	q->weight = 0;
	q->timeoutrestart = 0;
	q->periodicannouncefrequency = 0;
	q->randomperiodicannounce = 0;
	q->numperiodicannounce = 0;
	q->autopause = QUEUE_AUTOPAUSE_OFF;
	q->timeoutpriority = TIMEOUT_PRIORITY_APP;
	q->autopausedelay = 0;

	ast_string_field_set(q, sound_next, "queue-youarenext");
	ast_string_field_set(q, sound_thereare, "queue-thereare");
	ast_string_field_set(q, sound_calls, "queue-callswaiting");
	ast_string_field_set(q, queue_quantity1, "queue-quantity1");
	ast_string_field_set(q, queue_quantity2, "queue-quantity2");
	ast_string_field_set(q, sound_holdtime, "queue-holdtime");
	ast_string_field_set(q, sound_minutes, "queue-minutes");
	ast_string_field_set(q, sound_minute, "queue-minute");
	ast_string_field_set(q, sound_seconds, "queue-seconds");
	ast_string_field_set(q, sound_thanks, "queue-thankyou");
	ast_string_field_set(q, sound_reporthold, "queue-reporthold");

	if (!q->sound_periodicannounce[0]) {
		q->sound_periodicannounce[0] = ast_str_create(32);
	}

	if (q->sound_periodicannounce[0]) {
		ast_str_set(&q->sound_periodicannounce[0], 0, "queue-periodic-announce");
	}

	for (i = 1; i < MAX_PERIODIC_ANNOUNCEMENTS; i++) {
		if (q->sound_periodicannounce[i])
			ast_str_set(&q->sound_periodicannounce[i], 0, "%s", "");
	}

	q->reload = ast_tvnow();
	q->reload.tv_sec += 86400;
}

/*!
 * \brief Change queue penalty by adding rule.
 *
 * Check rule for errors with time or fomatting, see if rule is relative to rest
 * of queue, iterate list of rules to find correct insertion point, insert and return.
 * \retval -1 on failure
 * \retval 0 on success
 * \note Call this with the rule_lists locked
*/
static int insert_penaltychange(struct ao2_container *rules, const char *content, const int linenum)
{
	char *timestr, *maxstr, *minstr, *contentdup;
	struct penalty_rule *rule = NULL;
	int penaltychangetime;

	if (!(rule = ao2_alloc(sizeof(*rule), NULL))) {
		return -1;
	}

	contentdup = ast_strdupa(content);

	if (!(maxstr = strchr(contentdup, ','))) {
		ast_log(LOG_WARNING, "Improperly formatted penaltychange rule at line %d. Ignoring.\n", linenum);
		ao2_ref(rule, -1);
		return -1;
	}

	*maxstr++ = '\0';
	timestr = contentdup;

	if ((penaltychangetime = atoi(timestr)) < 0) {
		ast_log(LOG_WARNING, "Improper time parameter specified for penaltychange rule at line %d. Ignoring.\n", linenum);
		ao2_ref(rule, -1);
		return -1;
	}

	rule->time = penaltychangetime;

	if ((minstr = strchr(maxstr,',')))
		*minstr++ = '\0';
	
	/* The last check will evaluate true if either no penalty change is indicated for a given rule
	 * OR if a min penalty change is indicated but no max penalty change is */
	if (*maxstr == '+' || *maxstr == '-' || *maxstr == '\0') {
		rule->max_relative = 1;
	}

	rule->max_value = atoi(maxstr);

	if (!ast_strlen_zero(minstr)) {
		if (*minstr == '+' || *minstr == '-')
			rule->min_relative = 1;
		rule->min_value = atoi(minstr);
	} else /*there was no minimum specified, so assume this means no change*/
		rule->min_relative = 1;

	/*We have the rule made, now we need to insert it where it belongs*/
	ao2_link(rules, rule);
	ao2_ref(rule, -1);

	return 0;
}

/*! \brief return value for joinempty or leavewhenemty options*/
static enum empty_conditions parse_empty_options(const char *value, int joinempty)
{
	char *value_copy = ast_strdupa(value);
	char *option = NULL;
	enum empty_conditions empty = 0;

	while ((option = strsep(&value_copy, ","))) {
		if (!strcasecmp(option, "paused")) {
			empty |= QUEUE_EMPTY_PAUSED;
		} else if (!strcasecmp(option, "penalty")) {
			empty |= QUEUE_EMPTY_PENALTY;
		} else if (!strcasecmp(option, "inuse")) {
			empty |= QUEUE_EMPTY_INUSE;
		} else if (!strcasecmp(option, "ringing")) {
			empty |= QUEUE_EMPTY_RINGING;
		} else if (!strcasecmp(option, "invalid")) {
			empty |= QUEUE_EMPTY_INVALID;
		} else if (!strcasecmp(option, "wrapup")) {
			empty |= QUEUE_EMPTY_WRAPUP;
		} else if (!strcasecmp(option, "unavailable")) {
			empty |= QUEUE_EMPTY_UNAVAILABLE;
		} else if (!strcasecmp(option, "unknown")) {
			empty |= QUEUE_EMPTY_UNKNOWN;
		} else if (!strcasecmp(option, "loose")) {
			empty = (QUEUE_EMPTY_PENALTY | QUEUE_EMPTY_INVALID);
		} else if (!strcasecmp(option, "strict")) {
			empty = (QUEUE_EMPTY_PENALTY | QUEUE_EMPTY_INVALID | QUEUE_EMPTY_PAUSED | QUEUE_EMPTY_UNAVAILABLE);
		} else if ((ast_false(option) && joinempty) || (ast_true(option) && !joinempty)) {
			empty = (QUEUE_EMPTY_PENALTY | QUEUE_EMPTY_INVALID | QUEUE_EMPTY_PAUSED);
		} else if ((ast_false(option) && !joinempty) || (ast_true(option) && joinempty)) {
			empty = 0;
		} else {
			ast_log(LOG_WARNING, "Unknown option %s for '%s'\n", option, joinempty ? "joinempty" : "leavewhenempty");
		}
	}

	return empty;
}

/*! \brief Configure a queue parameter.
 *
 * The failunknown flag is set for config files (and static realtime) to show
 * errors for unknown parameters. It is cleared for dynamic realtime to allow
 *  extra fields in the tables.
 * \note For error reporting, line number is passed for .conf static configuration,
 * for Realtime queues, linenum is -1.
*/
static void queue_set_param(struct call_queue *q, const char *param, const char *val, int linenum, int failunknown)
{
	if (!strcasecmp(param, "musicclass") || 
		!strcasecmp(param, "music") || !strcasecmp(param, "musiconhold")) {
		ast_string_field_set(q, moh, val);
	} else if (!strcasecmp(param, "announce")) {
		ast_string_field_set(q, announce, val);
	} else if (!strcasecmp(param, "context")) {
		ast_string_field_set(q, context, val);
	} else if (!strcasecmp(param, "timeout")) {
		q->timeout = atoi(val);
		if (q->timeout < 0)
			q->timeout = DEFAULT_TIMEOUT;
	} else if (!strcasecmp(param, "ringinuse")) {
		q->ringinuse = ast_true(val);
	} else if (!strcasecmp(param, "setinterfacevar")) {
		q->setinterfacevar = ast_true(val);
	} else if (!strcasecmp(param, "setqueuevar")) {
		q->setqueuevar = ast_true(val);
	} else if (!strcasecmp(param, "setqueueentryvar")) {
		q->setqueueentryvar = ast_true(val);
	} else if (!strcasecmp(param, "monitor-format")) {
		ast_copy_string(q->monfmt, val, sizeof(q->monfmt));
	} else if (!strcasecmp(param, "membermacro")) {
		ast_string_field_set(q, membermacro, val);
	} else if (!strcasecmp(param, "membergosub")) {
		ast_string_field_set(q, membergosub, val);
	} else if (!strcasecmp(param, "queue-youarenext")) {
		ast_string_field_set(q, sound_next, val);
	} else if (!strcasecmp(param, "queue-thereare")) {
		ast_string_field_set(q, sound_thereare, val);
	} else if (!strcasecmp(param, "queue-callswaiting")) {
		ast_string_field_set(q, sound_calls, val);
	} else if (!strcasecmp(param, "queue-quantity1")) {
		ast_string_field_set(q, queue_quantity1, val);
	} else if (!strcasecmp(param, "queue-quantity2")) {
		ast_string_field_set(q, queue_quantity2, val);
	} else if (!strcasecmp(param, "queue-holdtime")) {
		ast_string_field_set(q, sound_holdtime, val);
	} else if (!strcasecmp(param, "queue-minutes")) {
		ast_string_field_set(q, sound_minutes, val);
	} else if (!strcasecmp(param, "queue-minute")) {
		ast_string_field_set(q, sound_minute, val);
	} else if (!strcasecmp(param, "queue-seconds")) {
		ast_string_field_set(q, sound_seconds, val);
	} else if (!strcasecmp(param, "queue-thankyou")) {
		ast_string_field_set(q, sound_thanks, val);
	} else if (!strcasecmp(param, "queue-callerannounce")) {
		ast_string_field_set(q, sound_callerannounce, val);
	} else if (!strcasecmp(param, "queue-reporthold")) {
		ast_string_field_set(q, sound_reporthold, val);
	} else if (!strcasecmp(param, "announce-frequency")) {
		q->announcefrequency = atoi(val);
	} else if (!strcasecmp(param, "min-announce-frequency")) {
		q->minannouncefrequency = atoi(val);
		ast_debug(1, "%s=%s for queue '%s'\n", param, val, q->name);
	} else if (!strcasecmp(param, "announce-round-seconds")) {
		q->roundingseconds = atoi(val);
		/* Rounding to any other values just doesn't make sense... */
		if (!(q->roundingseconds == 0 || q->roundingseconds == 5 || q->roundingseconds == 10
			|| q->roundingseconds == 15 || q->roundingseconds == 20 || q->roundingseconds == 30)) {
			if (linenum >= 0) {
				ast_log(LOG_WARNING, "'%s' isn't a valid value for %s "
					"using 0 instead for queue '%s' at line %d of queues.conf\n",
					val, param, q->name, linenum);
			} else {
				ast_log(LOG_WARNING, "'%s' isn't a valid value for %s "
					"using 0 instead for queue '%s'\n", val, param, q->name);
			}
			q->roundingseconds=0;
		}
	} else if (!strcasecmp(param, "announce-holdtime")) {
		if (!strcasecmp(val, "once"))
			q->announceholdtime = ANNOUNCEHOLDTIME_ONCE;
		else if (ast_true(val))
			q->announceholdtime = ANNOUNCEHOLDTIME_ALWAYS;
		else
			q->announceholdtime = 0;
	} else if (!strcasecmp(param, "announce-position")) {
		if (!strcasecmp(val, "limit"))
			q->announceposition = ANNOUNCEPOSITION_LIMIT;
		else if (!strcasecmp(val, "more"))
			q->announceposition = ANNOUNCEPOSITION_MORE_THAN;
		else if (ast_true(val))
			q->announceposition = ANNOUNCEPOSITION_YES;
		else
			q->announceposition = ANNOUNCEPOSITION_NO;
	} else if (!strcasecmp(param, "announce-position-limit")) {
		q->announcepositionlimit = atoi(val);
	} else if (!strcasecmp(param, "periodic-announce")) {
		if (strchr(val, ',')) {
			char *s, *buf = ast_strdupa(val);
			unsigned int i = 0;

			while ((s = strsep(&buf, ",|"))) {
				if (!q->sound_periodicannounce[i])
					q->sound_periodicannounce[i] = ast_str_create(16);
				ast_str_set(&q->sound_periodicannounce[i], 0, "%s", s);
				i++;
				if (i == MAX_PERIODIC_ANNOUNCEMENTS)
					break;
			}
			q->numperiodicannounce = i;
		} else {
			ast_str_set(&q->sound_periodicannounce[0], 0, "%s", val);
			q->numperiodicannounce = 1;
		}
	} else if (!strcasecmp(param, "periodic-announce-frequency")) {
		q->periodicannouncefrequency = atoi(val);
	} else if (!strcasecmp(param, "relative-periodic-announce")) {
		q->relativeperiodicannounce = ast_true(val);
	} else if (!strcasecmp(param, "random-periodic-announce")) {
		q->randomperiodicannounce = ast_true(val);
	} else if (!strcasecmp(param, "retry")) {
		q->retry = atoi(val);
		if (q->retry <= 0)
			q->retry = DEFAULT_RETRY;
	} else if (!strcasecmp(param, "wrapuptime")) {
		q->wrapuptime = atoi(val);
	} else if (!strcasecmp(param, "penaltymemberslimit")) {
		if ((sscanf(val, "%10d", &q->penaltymemberslimit) != 1)) {
			q->penaltymemberslimit = 0;
		}
	} else if (!strcasecmp(param, "autofill")) {
		q->autofill = ast_true(val);
	} else if (!strcasecmp(param, "monitor-type")) {
		if (!strcasecmp(val, "mixmonitor"))
			q->montype = 1;
	} else if (!strcasecmp(param, "autopause")) {
		q->autopause = autopause2int(val);
	} else if (!strcasecmp(param, "autopausedelay")) {
		q->autopausedelay = atoi(val);
	} else if (!strcasecmp(param, "autopausebusy")) {
		q->autopausebusy = ast_true(val);
	} else if (!strcasecmp(param, "autopauseunavail")) {
		q->autopauseunavail = ast_true(val);
	} else if (!strcasecmp(param, "maxlen")) {
		q->maxlen = atoi(val);
		if (q->maxlen < 0)
			q->maxlen = 0;
	} else if (!strcasecmp(param, "servicelevel")) {
		q->servicelevel= atoi(val);
	} else if (!strcasecmp(param, "strategy")) {
		int strategy;

		/* We are a static queue and already have set this, no need to do it again */
		if (failunknown) {
			return;
		}
		strategy = strat2int(val);
		if (strategy < 0) {
			ast_log(LOG_WARNING, "'%s' isn't a valid strategy for queue '%s', using ringall instead\n",
				val, q->name);
			q->strategy = QUEUE_STRATEGY_RINGALL;
		}
		if (strategy == q->strategy) {
			return;
		}
		if (strategy == QUEUE_STRATEGY_LINEAR) {
			ast_log(LOG_WARNING, "Changing to the linear strategy currently requires asterisk to be restarted.\n");
			return;
		}
		q->strategy = strategy;
	} else if (!strcasecmp(param, "joinempty")) {
		q->joinempty = parse_empty_options(val, 1);
	} else if (!strcasecmp(param, "leavewhenempty")) {
		q->leavewhenempty = parse_empty_options(val, 0);
	} else if (!strcasecmp(param, "eventmemberstatus")) {
		q->maskmemberstatus = !ast_true(val);
	} else if (!strcasecmp(param, "eventwhencalled")) {
		if (!strcasecmp(val, "vars")) {
			q->eventwhencalled = QUEUE_EVENT_VARIABLES;
		} else {
			q->eventwhencalled = ast_true(val) ? 1 : 0;
		}
	} else if (!strcasecmp(param, "reportholdtime")) {
		q->reportholdtime = ast_true(val);
	} else if (!strcasecmp(param, "memberdelay")) {
		q->memberdelay = atoi(val);
	} else if (!strcasecmp(param, "weight")) {
		q->weight = atoi(val);
	} else if (!strcasecmp(param, "timeoutrestart")) {
		q->timeoutrestart = ast_true(val);
	} else if (!strcasecmp(param, "defaultrule")) {
		ast_string_field_set(q, defaultrule, val);
	} else if (!strcasecmp(param, "timeoutpriority")) {
		if (!strcasecmp(val, "conf")) {
			q->timeoutpriority = TIMEOUT_PRIORITY_CONF;
		} else {
			q->timeoutpriority = TIMEOUT_PRIORITY_APP;
		}
	} else if (failunknown) {
		if (linenum >= 0) {
			ast_log(LOG_WARNING, "Unknown keyword in queue '%s': %s at line %d of queues.conf\n",
				q->name, param, linenum);
		} else {
			ast_log(LOG_WARNING, "Unknown keyword in queue '%s': %s\n", q->name, param);
		}
	}
}

/*! \brief callback that is called when a member is released*/
static void remove_queue_member(void *data) {
	struct member *mem = data;

	ast_string_field_free_memory(mem);

	unref_device(mem->device);
}

/*!
 * \brief Find rt member record to update otherwise create one.
 *
 * Search for member in queue, if found update penalty/paused state,
 * if no member exists create one flag it as a RT member and add to queue member list.
 *
 * \retval RES_NOT_DYNAMIC when they aren't a RT member
 * \retval RES_OKAY added member from queue
 * \retval RES_ERROR member was not ok
 * \retval RES_EXISTS queue exists but no members
 * \retval RES_OUTOFMEMORY queue exists but not enough memory to create member
*/
static int handle_member_record(struct call_queue *q, const char *interface, struct ast_config *member_config,
	enum member_type memtype, const char* source)
{
	struct member *m, *rt_m;
	struct mem_state *s;
	struct ast_variable *v;
	int link = 0, res = RES_OKAY;
	char *rt_uniqueid = NULL, *st_dev = NULL;
	int dead = 0;

	if (ast_strlen_zero(interface)) {
		ast_log(AST_LOG_ERROR, "Interface was not specified !!\n");
		return RES_ERROR;
	}

	if (!(m = ao2_find(q->data->members, (char *)interface, 0))) {
		if (!(m = ao2_alloc(sizeof(*m), remove_queue_member))) {
			return RES_OUTOFMEMORY;
		}
		if (ast_string_field_init(m, 64)) {
			ao2_ref(m, -1);
			return RES_OUTOFMEMORY;
		}

		m->device = NULL;
		m->paused = 0;
		m->callinuse = 1;
		if (memtype & QUEUE_ADD_MEMBER_REALTIME) {
			m->realtime = 1;
		} else if (memtype & QUEUE_ADD_MEMBER_DYNAMIC) {
			m->dynamic = 1;
		}
		m->dead = 0;
		m->calls = 0;
		m->lastcall = ast_tv(0, 0);
		m->lastwrapup = 0;
		link = 1;
		ast_string_field_set(m, interface, interface);
	} else {
		ao2_lock(q->data->members);

		if (memtype & QUEUE_ADD_MEMBER_DYNAMIC) {
			/* dynamic members are the lowest priority and cannot overwrite settings from DB*/
			if (m->dynamic) {
				res = RES_EXISTS;
			} else {
				res = RES_NOT_DYNAMIC;
			}
			ao2_unlock(q->data->members);
			ao2_ref(m, -1);
			return res;
		} else if ((m->dynamic || m->realtime) && (memtype & QUEUE_ADD_MEMBER_STATIC)) {
			/*static members take precedence over all others*/
			ao2_lock(m);
			m->dynamic = 0;
			m->realtime = 0;
			if (!ast_strlen_zero(m->rt_uniqueid)) {
				ast_string_field_set(m, rt_uniqueid, NULL);
			}
		} else if (memtype & QUEUE_ADD_MEMBER_REALTIME) {
			/* realtime takes precedence over dynamic but not static*/
			ao2_lock(m);
			if (m->dynamic) {
				m->dynamic = 0;
				m->realtime = 1;
			} else if (!m->realtime) {
				ao2_unlock(m);
				ao2_unlock(q->data->members);
				ao2_ref(m, -1);
				return RES_EXISTS;
			}
			m->dead = 0;
		} else {
			ao2_lock(m);
		}
		ao2_unlock(q->data->members);
	}

	for (v = ast_variable_browse(member_config, interface); v; v = v->next) {
		if (!ast_strlen_zero(v->value) && !strcasecmp(v->name, "uniqueid")) {
			rt_uniqueid = ast_strdupa(v->value);
		} else if (!strcasecmp(v->name, "membername")) {
			ast_string_field_set(m, membername, v->value);
		} else if (!strcasecmp(v->name, "state_interface")) {
			st_dev = ast_strdupa(ast_strlen_zero(v->value) ? interface : v->value);
		} else if (!strcasecmp(v->name, "penalty")) {
			if ((sscanf(v->value, "%30d", &m->penalty) != 1) || (!negative_penalty_invalid && m->penalty < 0)) {
				m->penalty = 0;
			} else if (m->penalty < 0) {
				/* negative_penalty_invalid is set and i have a invalid penalty ignoring this member */
				dead = 1;
			}
		} else if (!strcasecmp(v->name, "paused")) {
			m->paused = abs(ast_true(v->value));
		} else if (!strcasecmp(v->name, "callinuse") || !strcasecmp(v->name, "ignorebusy")) {
			m->callinuse = abs(ast_true(v->value));
		}
	}

	if (ast_strlen_zero(st_dev)) {
		st_dev = ast_strdupa(interface);
	}

	if (!dead && (s = ao2_find(devices, st_dev, 0))) {
		if ((s && (m->device != s)) || (!s && m->device)) {
			unref_device(m->device);
			m->device = (s) ? s : NULL;
		} else if (s) {
			unref_device(s);
		}
	}

	if (!dead && !m->device && !(m->device = create_member_state(st_dev))) {
		dead = 1;
	}

	if (ast_strlen_zero(m->membername)) {
		ast_string_field_set(m, membername, interface);
	}

	/*check the uniqueness of the RT uniqueid */
	if (!dead && link && (memtype & QUEUE_ADD_MEMBER_REALTIME)) {
		if (ast_strlen_zero(rt_uniqueid)) {
			ast_log(LOG_WARNING, "Realtime field uniqueid is empty for member %s\n", S_OR(m->membername, interface));
			dead = 1;
		} else if ((rt_m = ao2_callback(q->data->members, 0, member_cmp_uniqueid_fn, rt_uniqueid))) {
			/*make sure there no duplicates this should never happen am i changing interface perhaps ??*/
			dead = 1;
			ao2_lock(rt_m);
			ast_log(AST_LOG_WARNING, "Duplicate uniqueid found while adding %s (%s) found %s (%s) on queue %s : Not adding\n",
					m->interface, m->membername, rt_m->interface, rt_m->membername, q->name);
			ao2_unlock(rt_m);
			ao2_ref(rt_m, -1);
		} else {
			ast_string_field_set(m, rt_uniqueid, rt_uniqueid);
		}
	}

	if (!dead && link) {
		int status = get_device_status(m);

		/* i have just been born */
		if (!log_membername_as_agent) {
			ast_queue_log(q->name, source, m->interface, "ADDMEMBER", "%s", m->paused ? "PAUSED" : "");
		} else {
			ast_queue_log(q->name, source, m->membername, "ADDMEMBER", "%s", m->paused ? "PAUSED" : "");
		}
		manager_event(EVENT_FLAG_AGENT, "QueueMemberAdded",
			"Queue: %s\r\n"
			"Location: %s\r\n"
			"MemberName: %s\r\n"
			"StateInterface: %s\r\n"
			"Membership: %s\r\n"
			"Penalty: %d\r\n"
			"CallsTaken: %d\r\n"
			"LastCall: %d\r\n"
			"Status: %d\r\n"
			"Paused: %d\r\n"
			"CallInuse: %d\r\n",
			q->name, m->interface, m->membername, m->device->state_interface,
			m->dynamic ? "dynamic" : m->realtime ? "realtime" : "static",
			m->penalty, m->calls, (int)m->lastcall.tv_sec, status, m->paused, m->callinuse);
		ao2_link(q->data->members, m);
	} else if (dead) {
		/* ive failed penalty/uniqueid/devstate failure */
		if (!m->device) {
			res = RES_OUTOFMEMORY;
		} else {
			res = RES_ERROR;
		}
		if (!link) {
			/* thee was a config error remove this member from container now*/
			if (!log_membername_as_agent) {
				ast_queue_log(q->name, source, m->interface, "REMOVEMEMBER", "%s", "");
			} else {
				ast_queue_log(q->name, source, m->membername, "REMOVEMEMBER", "%s", "");
			}
			ao2_unlock(m);
			ao2_unlink(q->data->members, m);
		}
	} else if (!link) {
		/* ive been updated */
		ao2_unlock(m);
	}
	ao2_ref(m, -1);
	return res;
}

static void rt_load_member_config(struct call_queue *q)
{
	struct ast_config *member_config;
	char *interface = NULL;

	/* we may not have realtime members */
	if (!(member_config = ast_load_realtime_multientry("queue_members", "interface LIKE", "%", "queue_name", q->name, SENTINEL))) {
		ast_debug(3, "Queue %s has no realtime members defined. No need for update\n", q->name);
		return;
	}

	/* Temporarily set realtime members dead so we can detect deleted ones. */
	ao2_callback(q->data->members, OBJ_NODATA | OBJ_MULTIPLE, mark_realtime_member_dead, NULL);

	while ((interface = ast_category_browse(member_config, interface))) {
		handle_member_record(q, interface, member_config, QUEUE_ADD_MEMBER_REALTIME, "REALTIME");
	}
	ast_config_destroy(member_config);

	/* Delete all realtime members that have been deleted in DB. */
	ao2_callback_data(q->data->members, OBJ_NODATA | OBJ_MULTIPLE | OBJ_UNLINK, kill_realtime_dead_members, NULL, q);
}

/*! \brief Free queue's data struct */
static void destroy_queue_info(void *obj)
{
	struct queue_data *data = obj;

	ao2_callback(data->members, OBJ_UNLINK | OBJ_NODATA | OBJ_MULTIPLE, NULL, NULL);
	ao2_ref(data->members, -1);

	if (data->head) {
		AST_LIST_HEAD_DESTROY(data->head);
		ast_free(data->head);
	}
}

/*! \brief find or create a queue data structure*/
static struct queue_data *get_queue_data(const char *name)
{
	struct queue_data *data;

	/* ref will be held for each queue and one ref for container */
	if ((data = ao2_find(qdata, (char *)name, 0))) {
		return data;
	} else  if (!(data = ao2_alloc(sizeof(*data), destroy_queue_info))) {
		return NULL;
	}

	if (!(data->head = ast_calloc(1, sizeof(*data->head)))) {
		ao2_ref(data, -1);
		return NULL;
	}

	data->qhash = ast_str_case_hash(name);

	AST_LIST_HEAD_INIT(data->head);

	ao2_link(qdata, data);
	return data;
}

/*! \brief Free queue's member list then its string fields */
static void destroy_queue(void *obj)
{
	struct call_queue *q = obj;
	int i;

	ast_string_field_free_memory(q);
	for (i = 0; i < MAX_PERIODIC_ANNOUNCEMENTS; i++) {
		if (q->sound_periodicannounce[i])
			free(q->sound_periodicannounce[i]);
	}
	ao2_ref(q->data, -1);
}

/*! \brief create a new call_queue structure */
static struct call_queue *alloc_queue(const char *queuename, int rt)
{
	struct call_queue *q;

	if (!(q = ao2_t_alloc(sizeof(*q), destroy_queue, "Allocate queue"))) {
		return NULL;
	}

	if (!(q->data = get_queue_data(queuename))) {
		ao2_ref(q, -1);
		return NULL;
	}

	if (ast_string_field_init(q, 64)) {
		ao2_ref(q->data, -1);
		ao2_ref(q, -1);
		return NULL;
	}

	ast_string_field_set(q, name, queuename);
	q->realtime = rt;

	/* Ensure defaults for all parameters not set explicitly. */
	init_queue(q);

	return q;
}

/*
 *
 */
static struct call_queue *config_call_queue(struct call_queue *oldq, struct ast_variable *queue_vars, const char *queuename, int reload_members)
{
	int prev_weight = 0;
	struct ast_variable *v;
	char *tmp;
	const char *tmp_name;
	char tmpbuf[64];	/* Must be longer than the longest queue param name. */
	struct call_queue *q;

	/* Create a new queue if an in-core entry does not exist yet. */
	if (!oldq && !(q = alloc_queue(queuename, 1))) {
		ast_variables_destroy(queue_vars);
		return NULL;
	} else if (oldq) {
		prev_weight = oldq->weight ? 1 : 0;
		/*! \note The queue is recreated and the existing queue will not change and any
		 *users holding a ref to the queue will have no changes applied.
		 */
		if (!(q = alloc_queue(queuename, 1))) {
			/* i could not allocate new structure return the old one*/
			ast_log(AST_LOG_WARNING, "Failed to assign new queue object returning unchanged object\n");
			ast_variables_destroy(queue_vars);
			return NULL;
		}
	}

	memset(tmpbuf, 0, sizeof(tmpbuf));
	for (v = queue_vars; v; v = v->next) {
		/* Convert to dashes `-' from underscores `_' as the latter are more SQL friendly. */
		if ((tmp = strchr(v->name, '_'))) {
			ast_copy_string(tmpbuf, v->name, sizeof(tmpbuf));
			tmp_name = tmpbuf;
			tmp = tmpbuf;
			while ((tmp = strchr(tmp, '_')))
				*tmp++ = '-';
		} else
			tmp_name = v->name;

		/* NULL values don't get returned from realtime; blank values should
		 * still get set.  If someone doesn't want a value to be set, they
		 * should set the realtime column to NULL, not blank. */
		queue_set_param(q, tmp_name, v->value, -1, 0);
	}
	ast_variables_destroy(queue_vars);

	/* its important that this is never altered in the life of the queue*/
	if (!q->data->members && (q->strategy == QUEUE_STRATEGY_LINEAR || q->strategy == QUEUE_STRATEGY_RRORDERED)) {
		/* linear strategy depends on order, so we have to place all members in a single bucket */
		q->data->members = ao2_container_alloc(1, member_hash_fn, member_cmp_fn);
	} else if (!q->data->members) {
		q->data->members = ao2_container_alloc(37, member_hash_fn, member_cmp_fn);
	}

	/* update the use_weight value if the queue's has gained or lost a weight */
	if (!q->weight && prev_weight) {
		ast_atomic_fetchadd_int(&use_weight, -1);
	} else if (q->weight && !prev_weight) {
		ast_atomic_fetchadd_int(&use_weight, +1);
	}

	/* add persistent members to new queue*/
	if (!oldq && queue_persistent_members) {
		pm_load_member_config(q);
	}

	/* Load realtime members*/
	if (reload_members) {
		rt_load_member_config(q);
	}

	if (oldq) {
		ao2_lock(queues);
		ao2_find(queues, oldq, OBJ_UNLINK | OBJ_POINTER | OBJ_NODATA | OBJ_NOLOCK);
		ao2_link(queues, q);
		ao2_unlock(queues);
		ao2_ref(oldq, -1);
	} else {
		ao2_link(queues, q);
	}

	return q;
}

/*!
 * \brief Reload a single queue via realtime.
 *
 * Check for statically defined queue first, check if deleted RT queue,
 * check for new RT queue, if queue vars are not defined init them with defaults.
 * reload RT queue vars, set RT queue members dead and reload them, return finished queue.
 * \retval the queue,
 * \retval NULL if it doesn't exist.
*/
static struct call_queue *load_realtime_queue(const char *queuename, struct ast_flags *mask)
{
	struct ast_variable *queue_vars;
	struct call_queue *oldq;

	int reload_queue = (mask) ? ast_test_flag(mask, QUEUE_RELOAD_PARAMETERS) : 0;
	int reload_members = (mask) ? ast_test_flag(mask, QUEUE_RELOAD_MEMBER) : 0;
	int reload_realtime = (mask) ? ast_test_flag(mask, QUEUE_RELOAD_REALTIME) : 0;

	/* return if im not realtime or not reloading the queue possibly checking members */
	if ((oldq = ao2_t_find(queues, (char *)queuename, 0, "Look for queue in memory first")) &&
	    (!oldq->realtime || !(reload_queue || reload_realtime))) {
		if (reload_members) {
			rt_load_member_config(oldq);
		}
		return oldq;
	} else if (!oldq && !(reload_queue || reload_realtime)) {
		ast_debug(1, "Not loading queue %s at this time\n",queuename);
		return NULL;
	}

	/* if im reloading realtime (CLI/AMI) i ignore cache timer */
	if (!reload_realtime && oldq && !ast_tvzero(oldq->reload) &&
	    (ast_tvcmp(ast_tvnow(), oldq->reload) < 0)) {
		ast_debug(1, "Not reloading queue %s for next %ld Seconds\n", oldq->name, (long)ast_tvdiff_sec(oldq->reload, ast_tvnow()));
		return oldq;
	}

	/* Check if queue is defined in realtime if im reloading */
	if (!(queue_vars = ast_load_realtime("queues", "name", queuename, SENTINEL))) {
		/* Delete queue from in-core list if it has been deleted in realtime.
		 * ! \note On DB failure the queue will be removed as i cant distinguish a DB failure
		 */
		if (oldq) {
			ast_debug(1, "Queue %s not found in realtime.\n", queuename);
			ao2_t_unlink(queues, oldq, "Unused; removing from container");
			ao2_t_ref(oldq, -1, "Queue is dead; can't return it");
		}
		return NULL;
	}

	return config_call_queue(oldq, queue_vars, queuename, reload_members);
}

static int update_realtime_member_field(struct member *mem, const char *queue_name, const char *field, const char *value)
{
	int ret = -1;

	if (ast_strlen_zero(mem->rt_uniqueid)) {
		return ret;
	}

	if ((ast_update_realtime("queue_members", "uniqueid", mem->rt_uniqueid, field, value, SENTINEL)) > 0) {
		ret = 0;
	}

	return ret;
}

static void load_all_realtime_queues(struct ast_flags *mask)
{
	const char *queuename;
	struct ast_config *cfg;
	struct call_queue *queue;
	struct ast_category *cat;
	struct ast_variable *var;

	/* load realtime queues. */
	if ((cfg = ast_load_realtime_multientry("queues", "name LIKE", "%", SENTINEL))) {
		for (queuename = ast_category_browse(cfg, NULL);
				!ast_strlen_zero(queuename);
				queuename = ast_category_browse(cfg, queuename)) {
			cat = ast_category_get(cfg, queuename);
			var = ast_category_detach_variables(cat);
			queue = ao2_find(queues, (char *)queuename, 0);
			queue = config_call_queue(queue, var, queuename, 1);
			ao2_ref(queue, -1);

		}
		ast_config_destroy(cfg);
	}
}

static int join_queue(char *queuename, struct queue_ent *qe, enum queue_result *reason, int position)
{
	struct queue_ent *cur;
	int res = -1;
	int pos = 0;
	int inserted = 0;
	struct ast_flags qflags = {QUEUE_RELOAD_PARAMETERS | QUEUE_RELOAD_MEMBER};

	/*obtain a ref for the queue reload realtime settings/members*/
	if (!(qe->parent = load_realtime_queue(queuename, &qflags))) {
		return res;
	}

	/* This is our one */
	if (get_member_status(qe, 1)) {
		*reason = QUEUE_JOINEMPTY;
		ao2_t_ref(qe->parent, -1, "Done with realtime queue");
		return res;
	}

	ao2_lock(qe->parent->data);
	if ((*reason == QUEUE_UNKNOWN && qe->parent->maxlen && (qe->parent->data->count >= qe->parent->maxlen)) ||
	    (*reason != QUEUE_UNKNOWN)) {
		ao2_unlock(qe->parent->data);
		*reason = QUEUE_FULL;
		ao2_t_ref(qe->parent, -1, "Done with realtime queue");

		return res;
	}
	ao2_unlock(qe->parent->data);


	/* There's space for us, put us at the right position inside
	 * the queue.
	 * Take into account the priority of the calling user */
	inserted = 0;

	AST_LIST_LOCK(qe->parent->data->head);
	AST_LIST_TRAVERSE_SAFE_BEGIN(qe->parent->data->head, cur, next) {
		/* We have higher priority than the current user, enter
		 * before him, after all the other users with priority
		 * higher or equal to our priority. */
		if (!inserted && qe && (qe->prio > cur->prio)) {
			AST_LIST_INSERT_BEFORE_CURRENT(qe, next);
			insert_entry(qe, &pos);
			inserted = 1;
		}
		/* <= is necessary for the position comparison because it may not be possible to enter
		 * at our desired position since higher-priority callers may have taken the position we want
		 */
		if (!inserted && qe && (qe->prio >= cur->prio) && position && (position <= pos + 1)) {
			AST_LIST_INSERT_BEFORE_CURRENT(qe, next);
			insert_entry(qe, &pos);
			/*pos is incremented inside insert_entry, so don't need to add 1 here*/
			if (position < pos) {
				ast_log(LOG_NOTICE, "Asked to be inserted at position %d but forced into position %d due to higher priority callers\n", position, pos);
			}
			inserted = 1;
		}
		cur->pos = ++pos;
	}
	AST_LIST_TRAVERSE_SAFE_END;

	/* No luck, join at the end of the queue */
	if (!inserted && qe) {
		AST_LIST_INSERT_TAIL(qe->parent->data->head, qe, next);
		insert_entry(qe, &pos);
	}
	AST_LIST_UNLOCK(qe->parent->data->head);

	/* pass a ref to the queue rules or this queue*/
	qe->pr = NULL;
	if ((qe->rules = ao2_find(rules, (char *)qe->parent->defaultrule, 0))) {
		int time = 0;
		ao2_callback_data(qe->rules->rules, OBJ_NODATA | OBJ_MULTIPLE, get_best_rule_cb, &time, &qe->pr);
	}

	res = 0;
	ao2_lock(qe->parent->data);
	ast_manager_event(qe->chan, EVENT_FLAG_CALL, "Join",
		"Channel: %s\r\n"
		"CallerIDNum: %s\r\n"
		"CallerIDName: %s\r\n"
		"ConnectedLineNum: %s\r\n"
		"ConnectedLineName: %s\r\n"
		"Queue: %s\r\n"
		"Position: %d\r\n"
		"Count: %d\r\n"
		"Uniqueid: %s\r\n",
		qe->chan->name,
		S_COR(qe->chan->caller.id.number.valid, qe->chan->caller.id.number.str, "unknown"),/* XXX somewhere else it is <unknown> */
		S_COR(qe->chan->caller.id.name.valid, qe->chan->caller.id.name.str, "unknown"),
		S_COR(qe->chan->connected.id.number.valid, qe->chan->connected.id.number.str, "unknown"),/* XXX somewhere else it is <unknown> */
		S_COR(qe->chan->connected.id.name.valid, qe->chan->connected.id.name.str, "unknown"),
		qe->parent->name, qe->pos, qe->parent->data->count, qe->chan->uniqueid );
	ao2_unlock(qe->parent->data);
	ast_debug(1, "Queue '%s' Join, Channel '%s', Position '%d'\n", qe->parent->name, qe->chan->name, qe->pos );

	return res;
}

static int play_file(struct ast_channel *chan, const char *filename)
{
	int res;

	if (ast_strlen_zero(filename)) {
		return 0;
	}

	if (!ast_fileexists(filename, NULL, chan->language)) {
		return 0;
	}

	ast_stopstream(chan);

	res = ast_streamfile(chan, filename, chan->language);
	if (!res)
		res = ast_waitstream(chan, AST_DIGIT_ANY);

	ast_stopstream(chan);

	return res;
}

/*!
 * \brief Check for valid exit from queue via goto
 * \retval 0 if failure
 * \retval 1 if successful
*/
static int valid_exit(struct queue_ent *qe, char digit)
{
	int digitlen = strlen(qe->digits);

	/* Prevent possible buffer overflow */
	if (digitlen < sizeof(qe->digits) - 2) {
		qe->digits[digitlen] = digit;
		qe->digits[digitlen + 1] = '\0';
	} else {
		qe->digits[0] = '\0';
		return 0;
	}

	/* If there's no context to goto, short-circuit */
	if (ast_strlen_zero(qe->parent->context))
		return 0;

	/* If the extension is bad, then reset the digits to blank */
	if (!ast_canmatch_extension(qe->chan, qe->parent->context, qe->digits, 1,
		S_COR(qe->chan->caller.id.number.valid, qe->chan->caller.id.number.str, NULL))) {
		qe->digits[0] = '\0';
		return 0;
	}

	/* We have an exact match */
	if (!ast_goto_if_exists(qe->chan, qe->parent->context, qe->digits, 1)) {
		qe->valid_digits = 1;
		/* Return 1 on a successful goto */
		return 1;
	}

	return 0;
}

static int say_position(struct queue_ent *qe, int ringing)
{
	int res = 0, avgholdmins, avgholdsecs, announceposition = 0;
	int say_thanks = 1;
	struct timeval now;

	/* Let minannouncefrequency seconds pass between the start of each position announcement */
	now = ast_tvnow();
	if (ast_tvdiff_sec(now, qe->last_pos) < qe->parent->minannouncefrequency) {
		return 0;
	}

	/* If either our position has changed, or we are over the freq timer, say position */
	if ((qe->last_pos_said == qe->pos) && (ast_tvdiff_sec(now, qe->last_pos) < qe->parent->announcefrequency)) {
		return 0;
	}

	if (ringing) {
		ast_indicate(qe->chan,-1);
	} else {
		ast_moh_stop(qe->chan);
	}

	if (qe->parent->announceposition == ANNOUNCEPOSITION_YES ||
		qe->parent->announceposition == ANNOUNCEPOSITION_MORE_THAN ||
		(qe->parent->announceposition == ANNOUNCEPOSITION_LIMIT &&
		qe->pos <= qe->parent->announcepositionlimit))
			announceposition = 1;


	if (announceposition == 1) {
		/* Say we're next, if we are */
		if (qe->pos == 1) {
			res = play_file(qe->chan, qe->parent->sound_next);
			if (res)
				goto playout;
			else
				goto posout;
		} else {
			if (qe->parent->announceposition == ANNOUNCEPOSITION_MORE_THAN && qe->pos > qe->parent->announcepositionlimit){
				/* More than Case*/
				res = play_file(qe->chan, qe->parent->queue_quantity1);
				if (res)
					goto playout;
				res = ast_say_number(qe->chan, qe->parent->announcepositionlimit, AST_DIGIT_ANY, qe->chan->language, NULL); /* Needs gender */
				if (res)
					goto playout;
			} else {
				/* Normal Case */
				res = play_file(qe->chan, qe->parent->sound_thereare);
				if (res)
					goto playout;
				res = ast_say_number(qe->chan, qe->pos, AST_DIGIT_ANY, qe->chan->language, NULL); /* Needs gender */
				if (res)
					goto playout;
			}
			if (qe->parent->announceposition == ANNOUNCEPOSITION_MORE_THAN && qe->pos > qe->parent->announcepositionlimit){
				/* More than Case*/
				res = play_file(qe->chan, qe->parent->queue_quantity2);
				if (res)
					goto playout;
			} else {
				res = play_file(qe->chan, qe->parent->sound_calls);
				if (res)
					goto playout;
			}
		}
	}
	ao2_lock(qe->parent->data);
	/* Round hold time to nearest minute */
	avgholdmins = abs(((qe->parent->data->holdtime + 30) - (ast_tvdiff_sec(ast_tvnow(), qe->start))) / 60);

	/* If they have specified a rounding then round the seconds as well */
	if (qe->parent->roundingseconds) {
		avgholdsecs = (abs(((qe->parent->data->holdtime + 30) - (ast_tvdiff_sec(ast_tvnow(), qe->start)))) - 60 * avgholdmins) / qe->parent->roundingseconds;
		avgholdsecs *= qe->parent->roundingseconds;
	} else {
		avgholdsecs = 0;
	}
	ao2_unlock(qe->parent->data);

	ast_verb(3, "Hold time for %s is %d minute(s) %d seconds\n", qe->parent->name, avgholdmins, avgholdsecs);

	/* If the hold time is >1 min, if it's enabled, and if it's not
	   supposed to be only once and we have already said it, say it */
    if ((avgholdmins+avgholdsecs) > 0 && qe->parent->announceholdtime &&
        ((qe->parent->announceholdtime == ANNOUNCEHOLDTIME_ONCE && ast_tvzero(qe->last_pos)) ||
        !(qe->parent->announceholdtime == ANNOUNCEHOLDTIME_ONCE))) {
		res = play_file(qe->chan, qe->parent->sound_holdtime);
		if (res)
			goto playout;

		if (avgholdmins >= 1) {
			res = ast_say_number(qe->chan, avgholdmins, AST_DIGIT_ANY, qe->chan->language, NULL);
			if (res)
				goto playout;

			if (avgholdmins == 1) {
				res = play_file(qe->chan, qe->parent->sound_minute);
				if (res)
					goto playout;
			} else {
				res = play_file(qe->chan, qe->parent->sound_minutes);
				if (res)
					goto playout;
			}
		}
		if (avgholdsecs >= 1) {
			res = ast_say_number(qe->chan, avgholdsecs, AST_DIGIT_ANY, qe->chan->language, NULL);
			if (res)
				goto playout;

			res = play_file(qe->chan, qe->parent->sound_seconds);
			if (res)
				goto playout;
		}
	} else if (qe->parent->announceholdtime && !qe->parent->announceposition) {
		say_thanks = 0;
	}

posout:
	if (qe->parent->announceposition) {
		ast_verb(3, "Told %s in %s their queue position (which was %d)\n",
			qe->chan->name, qe->parent->name, qe->pos);
	}
	if (say_thanks) {
		res = play_file(qe->chan, qe->parent->sound_thanks);
	}
playout:

	if ((res > 0 && !valid_exit(qe, res)))
		res = 0;

	/* Set our last_pos indicators */
	qe->last_pos = now;
	qe->last_pos_said = qe->pos;

	/* Don't restart music on hold if we're about to exit the caller from the queue */
	if (!res) {
		if (ringing) {
			ast_indicate(qe->chan, AST_CONTROL_RINGING);
		} else {
			ast_moh_start(qe->chan, qe->parent->moh, NULL);
		}
	}
	return res;
}

static void recalc_holdtime(struct queue_ent *qe, int newholdtime)
{
	int oldvalue;

	/* Calculate holdtime using an exponential average */
	/* Thanks to SRT for this contribution */
	/* 2^2 (4) is the filter coefficient; a higher exponent would give old entries more weight */

	ao2_lock(qe->parent->data);
	oldvalue = qe->parent->data->holdtime;
	qe->parent->data->holdtime = (((oldvalue << 2) - oldvalue) + newholdtime) >> 2;
	ao2_unlock(qe->parent->data);
}

/*! \brief Caller leaving queue.
 *
 * Search the queue to find the leaving client, if found remove from queue
 * create manager event, move others up the queue.
*/
static void leave_queue(struct queue_ent *qe)
{
	struct call_queue *q;
	struct queue_ent *cur;
	int pos = 0;
	char posstr[20];

	if (!(q = qe->parent)) {
		return;
	}

	AST_LIST_LOCK(q->data->head);
	AST_LIST_TRAVERSE_SAFE_BEGIN(q->data->head, cur, next) {
		if (cur == qe) {
			ao2_lock(q->data);
			q->data->count--;

			/* Take us out of the queue */
			ast_manager_event(qe->chan, EVENT_FLAG_CALL, "Leave",
				"Channel: %s\r\nQueue: %s\r\nCount: %d\r\nPosition: %d\r\nUniqueid: %s\r\n",
				qe->chan->name, q->name,  q->data->count, qe->pos, qe->chan->uniqueid);
			ao2_unlock(q->data);
			ast_debug(1, "Queue '%s' Leave, Channel '%s'\n", q->name, qe->chan->name );
			/* Take us out of the queue */
			AST_LIST_REMOVE_CURRENT(next);
			snprintf(posstr, sizeof(posstr), "%d", qe->pos);
			pbx_builtin_setvar_helper(qe->chan, "QUEUEPOSITION", posstr);
		} else {
			/* Renumber the people after us in the queue based on a new count */
			cur->pos = ++pos;
		}
	}
	AST_LIST_TRAVERSE_SAFE_END;
	AST_LIST_UNLOCK(q->data->head);
}

/*!
 * \internal
 * \brief Destroy the given callattempt structure and free it.
 * \since 1.8
 *
 * \param doomed callattempt structure to destroy.
 *
 * \return Nothing
 */
static void callattempt_free(void *data)
{
	struct callattempt *doomed = data;
	struct mem_state *s;

	if (doomed->member) {
		if (doomed->reserved || doomed->active) {
			ao2_lock(doomed->member);
			s = doomed->member->device;
			ao2_lock(s);
			if (doomed->reserved) {
				s->reserved--;
			}
			if (doomed->active) {
				s->active--;
			}
			ao2_unlock(s);
			ao2_unlock(doomed->member);
		}
		ao2_ref(doomed->member, -1);
	}
	ast_party_connected_line_free(&doomed->connected);
}

/*! \brief Hang up a list of outgoing calls */
static void hangupcalls(struct queue_ent *qe, struct callattempt *exception)
{
	struct callattempt *outgoing;
	struct ao2_iterator aiter;

	aiter = ao2_iterator_init(qe->attempts, 0);
	while ((outgoing = ao2_iterator_next(&aiter))) {
		/* If someone else answered the call we should indicate this in the CANCEL */
		/* Hangup any existing lines we have open */
		if (outgoing->chan && (outgoing != exception)) {
			if (exception || qe->cancel_answered_elsewhere) {
				ast_set_flag(outgoing->chan, AST_FLAG_ANSWERED_ELSEWHERE);
			}
			ast_hangup(outgoing->chan);
			ao2_unlink(qe->attempts, outgoing);
		} else if (outgoing != exception) {
			ao2_unlink(qe->attempts, outgoing);
		}
		ast_aoc_destroy_decoded(outgoing->aoc_s_rate_list);
		ao2_ref(outgoing, -1);
	}
	ao2_iterator_destroy(&aiter);
}

/*!
 * \brief Get the number of members available to accept a call.
 *
 * \note The queue passed in should be locked prior to this function call
 *
 * \param[in] q The queue for which we are couting the number of available members
 * \return Return the number of available members in queue q
 */
static int num_available_members(struct call_queue *q)
{
	struct member *mem;
	int avl = 0;
	struct ao2_iterator mem_iter;

	mem_iter = ao2_iterator_init(q->data->members, 0);
	while ((mem = ao2_iterator_next(&mem_iter))) {
		ao2_lock(mem);
		switch (get_device_status(mem)) {
			case AST_DEVICE_INVALID:
			case AST_DEVICE_UNAVAILABLE:
			case AST_DEVICE_BUSY:
				break;
			case AST_DEVICE_INUSE:
			case AST_DEVICE_RINGING:
			case AST_DEVICE_RINGINUSE:
			case AST_DEVICE_ONHOLD:
				if (!q->ringinuse || !mem->callinuse) {
					break;
				}
				/* else fall through */
			case AST_DEVICE_NOT_INUSE:
			case AST_DEVICE_UNKNOWN:
				if (!mem->paused) {
					avl++;
				}
				break;
		}
		ao2_unlock(mem);
		ao2_ref(mem, -1);

		/* If autofill is not enabled or if the queue's strategy is ringall, then
		 * we really don't care about the number of available members so much as we
		 * do that there is at least one available.
		 *
		 * In fact, we purposely will return from this function stating that only
		 * one member is available if either of those conditions hold. That way,
		 * functions which determine what action to take based on the number of available
		 * members will operate properly. The reasoning is that even if multiple
		 * members are available, only the head caller can actually be serviced.
		 */
		if ((!q->autofill || q->strategy == QUEUE_STRATEGY_RINGALL) && avl) {
			break;
		}
	}
	ao2_iterator_destroy(&mem_iter);

	return avl;
}

/* traverse all defined queues which have calls waiting and contain this member
   return 0 if no other queue has precedence (higher weight) or 1 if found  */
static int compare_weight(struct call_queue *rq, const char *interface)
{
	struct call_queue *q;
	struct member *mem;
	int count;
	int res = 0;
	struct ao2_iterator queue_iter;

	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate through queues"))) {
		/* don't check myself or queues with  lower weight*/
		if ((q == rq) || (q->weight <= rq->weight)) {
			ao2_ref(q, -1);
			continue;
		}
		ao2_lock(q->data);
		count = q->data->count;
		ao2_unlock(q->data);
		if (count && (mem = interface_exists(q, interface)) &&
		    (count >= num_available_members(q))) {
			ao2_ref(mem, -1);
			ast_debug(1, "Queue '%s' (weight %d, calls %d) is preferred over '%s' (weight %d)\n",
					q->name, q->weight, count, rq->name, rq->weight);
			ao2_ref(q, -1);
			res = 1;
			break;
		} else if (mem) {
			ao2_ref(mem, -1);
		}
		ao2_ref(q, -1);
	}
	ao2_iterator_destroy(&queue_iter);
	return res;
}

/*! \brief common hangup actions */
static void do_hang(struct callattempt *o)
{
	o->stillgoing = 0;
	ast_hangup(o->chan);
	o->chan = NULL;
}

/*! \brief convert "\n" to "\nVariable: " ready for manager to use */
static char *vars2manager(struct ast_channel *chan, char *vars, size_t len)
{
	struct ast_str *buf = ast_str_thread_get(&ast_str_thread_global_buf, len + 1);
	const char *tmp;

	if (pbx_builtin_serialize_variables(chan, &buf)) {
		int i, j;

		/* convert "\n" to "\nVariable: " */
		strcpy(vars, "Variable: ");
		tmp = ast_str_buffer(buf);

		for (i = 0, j = 10; (i < len - 1) && (j < len - 1); i++, j++) {
			vars[j] = tmp[i];

			if (tmp[i + 1] == '\0')
				break;
			if (tmp[i] == '\n') {
				vars[j++] = '\r';
				vars[j++] = '\n';

				ast_copy_string(&(vars[j]), "Variable: ", len - j);
				j += 9;
			}
		}
		if (j > len - 3)
			j = len - 3;
		vars[j++] = '\r';
		vars[j++] = '\n';
		vars[j] = '\0';
	} else {
		/* there are no channel variables; leave it blank */
		*vars = '\0';
	}
	return vars;
}

/*!
 * \brief Part 2 of ring_one
 *
 * Does error checking before attempting to request a channel and call a member.
 * This function is only called from ring_one().
 * Failure can occur if:
 * - Priority by another queue
 * - Member is paused
 * - Wrapup time not expired
 * - Member on call / or is not available for a call
 * - Channel cannot be created by driver
 * - Channel cannot be called by driver
 *
 * \retval 1 on success to reach a free agent
 * \retval 0 on failure to get agent.
 */
static int ring_entry(struct queue_ent *qe, struct callattempt *tmp, int *busies)
{
	int res;
	int status;
	char tech[256];
	char *location;
	const char *macrocontext, *macroexten;
	int dstat;

	/* we cannot take this call there is a more urgent call we qualify for */
	if (use_weight && compare_weight(qe->parent,tmp->member->interface)) {
		ast_debug(1, "Priority queue delaying call to %s:%s\n", qe->parent->name, tmp->member->interface);
		if (qe->chan->cdr) {
			ast_cdr_busy(qe->chan->cdr);
		}
		tmp->stillgoing = 0;
		(*busies)++;
		return 0;
	}

	ao2_lock(tmp->member);
	/* im paused i cannot take this call */
	if (tmp->member->paused) {
		ao2_unlock(tmp->member);
		ast_debug(1, "%s paused, can't receive call\n", tmp->member->interface);
		if (qe->chan->cdr) {
			ast_cdr_busy(qe->chan->cdr);
		}
		tmp->stillgoing = 0;
		(*busies)++;
		return 0;
	}

	/* am i still in wrapuptime */
	if (tmp->member->lastwrapup && (ast_tvdiff_sec(ast_tvnow(), tmp->member->lastcall) <= tmp->member->lastwrapup)) {
		ao2_unlock(tmp->member);
		ast_debug(1, "Wrapuptime not yet expired for %s\n", tmp->member->interface);
		if (qe->chan->cdr) {
			ast_cdr_busy(qe->chan->cdr);
		}
		tmp->stillgoing = 0;
		(*busies)++;
		return 0;
	}

	/* do not ring a member that is not able to take a call */
	dstat = get_device_status(tmp->member);
	if ((dstat == AST_DEVICE_INVALID) ||
	    (dstat == AST_DEVICE_BUSY) ||
	    (dstat == AST_DEVICE_UNAVAILABLE) ||
	    (!qe->parent->ringinuse && (dstat != AST_DEVICE_NOT_INUSE) && (dstat != AST_DEVICE_UNKNOWN))) {
		ao2_unlock(tmp->member);
		ast_debug(1, "%s is %s, can't receive call\n", tmp->member->interface, ast_devstate2str(dstat));
		if (qe->chan->cdr) {
			ast_cdr_busy(qe->chan->cdr);
		}
		tmp->stillgoing = 0;
		(*busies)++;
		return 0;
	}

	/* mark device and call entry reserved */
	if (!tmp->reserved) {
		struct mem_state *s = tmp->member->device;
		ao2_lock(s);
		s->reserved++;
		ao2_unlock(s);
		tmp->reserved = 1;
	}
	ao2_unlock(tmp->member);

	ast_copy_string(tech, tmp->member->interface, sizeof(tech));
	if ((location = strchr(tech, '/'))) {
		*location++ = '\0';
	} else {
		location = "";
	}

	/* Request the peer */
	if (!(tmp->chan = ast_request(tech, qe->chan->nativeformats, qe->chan, location, &status))) {
		if (qe->chan->cdr) {
			ast_cdr_busy(qe->chan->cdr);
		}
		tmp->stillgoing = 0;

		set_queue_member_status(tmp->member);
		ao2_lock(qe->parent->data);
		qe->parent->data->rrpos++;
		ao2_unlock(qe->parent->data);
		qe->linpos++;

		(*busies)++;
		return 0;
	}

	ast_channel_lock_both(tmp->chan, qe->chan);

	if (qe->cancel_answered_elsewhere) {
		ast_set_flag(tmp->chan, AST_FLAG_ANSWERED_ELSEWHERE);
	}
	tmp->chan->appl = "AppQueue";
	tmp->chan->data = "(Outgoing Line)";
	memset(&tmp->chan->whentohangup, 0, sizeof(tmp->chan->whentohangup));

	/* If the new channel has no callerid, try to guess what it should be */
	if (!tmp->chan->caller.id.number.valid) {
		if (qe->chan->connected.id.number.valid) {
			struct ast_party_caller caller;

			ast_party_caller_set_init(&caller, &tmp->chan->caller);
			caller.id = qe->chan->connected.id;
			caller.ani = qe->chan->connected.ani;
			ast_channel_set_caller_event(tmp->chan, &caller, NULL);
		} else if (!ast_strlen_zero(qe->chan->dialed.number.str)) {
			ast_set_callerid(tmp->chan, qe->chan->dialed.number.str, NULL, NULL);
		} else if (!ast_strlen_zero(S_OR(qe->chan->macroexten, qe->chan->exten))) {
			ast_set_callerid(tmp->chan, S_OR(qe->chan->macroexten, qe->chan->exten), NULL, NULL); 
		}
		tmp->dial_callerid_absent = 1;
	}

	ast_party_redirecting_copy(&tmp->chan->redirecting, &qe->chan->redirecting);

	tmp->chan->dialed.transit_network_select = qe->chan->dialed.transit_network_select;

	ast_connected_line_copy_from_caller(&tmp->chan->connected, &qe->chan->caller);

	/* Inherit specially named variables from parent channel */
	ast_channel_inherit_variables(qe->chan, tmp->chan);
	ast_channel_datastore_inherit(qe->chan, tmp->chan);

	/* Presense of ADSI CPE on outgoing channel follows ours */
	tmp->chan->adsicpe = qe->chan->adsicpe;

	/* Inherit context and extension */
	macrocontext = pbx_builtin_getvar_helper(qe->chan, "MACRO_CONTEXT");
	ast_string_field_set(tmp->chan, dialcontext, ast_strlen_zero(macrocontext) ? qe->chan->context : macrocontext);
	macroexten = pbx_builtin_getvar_helper(qe->chan, "MACRO_EXTEN");
	if (!ast_strlen_zero(macroexten))
		ast_copy_string(tmp->chan->exten, macroexten, sizeof(tmp->chan->exten));
	else
		ast_copy_string(tmp->chan->exten, qe->chan->exten, sizeof(tmp->chan->exten));
	if (ast_cdr_isset_unanswered()) {
		/* they want to see the unanswered dial attempts! */
		/* set up the CDR fields on all the CDRs to give sensical information */
		ast_cdr_setdestchan(tmp->chan->cdr, tmp->chan->name);
		strcpy(tmp->chan->cdr->clid, qe->chan->cdr->clid);
		strcpy(tmp->chan->cdr->channel, qe->chan->cdr->channel);
		strcpy(tmp->chan->cdr->src, qe->chan->cdr->src);
		strcpy(tmp->chan->cdr->dst, qe->chan->exten);
		strcpy(tmp->chan->cdr->dcontext, qe->chan->context);
		strcpy(tmp->chan->cdr->lastapp, qe->chan->cdr->lastapp);
		strcpy(tmp->chan->cdr->lastdata, qe->chan->cdr->lastdata);
		tmp->chan->cdr->amaflags = qe->chan->cdr->amaflags;
		strcpy(tmp->chan->cdr->accountcode, qe->chan->cdr->accountcode);
		strcpy(tmp->chan->cdr->userfield, qe->chan->cdr->userfield);
	}

	ast_channel_unlock(tmp->chan);
	ast_channel_unlock(qe->chan);

	/* Place the call, but don't wait on the answer */
	if ((res = ast_call(tmp->chan, location, 0))) {
		ast_debug(1, "ast call on peer returned %d\n", res);
		ast_verb(3, "Couldn't call %s\n", tmp->member->interface);
		do_hang(tmp);
		(*busies)++;
		tmp->stillgoing = 0;
		set_queue_member_status(tmp->member);
		return 0;
	} else if (qe->parent->eventwhencalled) {
		char vars[2048];

		ast_channel_lock_both(tmp->chan, qe->chan);
		ao2_lock(tmp->member);
		manager_event(EVENT_FLAG_AGENT, "AgentCalled",
			"Queue: %s\r\n"
			"AgentCalled: %s\r\n"
			"AgentName: %s\r\n"
			"ChannelCalling: %s\r\n"
			"DestinationChannel: %s\r\n"
			"CallerIDNum: %s\r\n"
			"CallerIDName: %s\r\n"
			"ConnectedLineNum: %s\r\n"
			"ConnectedLineName: %s\r\n"
			"Context: %s\r\n"
			"Extension: %s\r\n"
			"Priority: %d\r\n"
			"Uniqueid: %s\r\n"
			"%s",
			qe->parent->name, tmp->member->interface, tmp->member->membername, qe->chan->name, tmp->chan->name,
			S_COR(tmp->chan->caller.id.number.valid, tmp->chan->caller.id.number.str, "unknown"),
			S_COR(tmp->chan->caller.id.name.valid, tmp->chan->caller.id.name.str, "unknown"),
			S_COR(tmp->chan->connected.id.number.valid, tmp->chan->connected.id.number.str, "unknown"),
			S_COR(tmp->chan->connected.id.name.valid, tmp->chan->connected.id.name.str, "unknown"),
			qe->chan->context, qe->chan->exten, qe->chan->priority, qe->chan->uniqueid,
			qe->parent->eventwhencalled == QUEUE_EVENT_VARIABLES ? vars2manager(qe->chan, vars, sizeof(vars)) : "");

		ao2_unlock(tmp->member);
		ast_channel_unlock(tmp->chan);
		ast_channel_unlock(qe->chan);

		ast_verb(3, "Called %s\n", tmp->member->interface);
	}

	return 1;
}

/*!
 * \brief Place a call to a queue member.
 *
 * Once metrics have been calculated for each member, this function is used
 * to place a call to the appropriate member (or members). The low-level
 * channel-handling and error detection is handled in ring_entry
 *
 * \retval 1 if a member was called successfully
 * \retval 0 otherwise
 */
static int ring_one(struct queue_ent *qe, int *busies)
{
	int ret = 0;
	struct callattempt *cur, *best;
	struct ao2_iterator aiter;

	while (ret == 0) {
		best = NULL;
		ao2_callback_data(qe->attempts, OBJ_NODATA | OBJ_MULTIPLE, get_best_metric_cb, NULL, &best);
		if (!best) {
			ast_debug(1, "Nobody left to try ringing in queue\n");
			break;
		}
		if (qe->parent->strategy == QUEUE_STRATEGY_RINGALL) {
			/* Ring everyone who shares this best metric (for ringall) */
			aiter = ao2_iterator_init(qe->attempts, 0);
			while ((cur = ao2_iterator_next(&aiter))) {
				if (cur->stillgoing && !cur->chan && cur->metric <= best->metric) {
					ast_debug(1, "(Parallel) Trying '%s' with metric %d\n", cur->member->interface, cur->metric);
					ret |= ring_entry(qe, cur, busies);
				}
				ao2_ref(cur, -1);
			}
			ao2_iterator_destroy(&aiter);
		} else {
			/* Ring just the best channel */
			ast_debug(1, "Trying '%s' with metric %d\n", best->member->interface, best->metric);
			ret = ring_entry(qe, best, busies);
		}
		ao2_ref(best, -1);

		/* If we have timed out, break out */
		if (!ast_tvzero(qe->expire) && (ast_tvcmp(ast_tvnow(), qe->expire) >= 0)) {
			ast_debug(1, "Queue timed out while ringing members.\n");
			ret = 0;
			break;
		}
	}

	return ret;
}

/*! \brief Search for best metric and add to Round Robbin queue
 */
static int store_next_rr(struct queue_ent *qe)
{
	struct callattempt *best = NULL;
	struct queue_data *data = qe->parent->data;

	ao2_callback_data(qe->attempts, OBJ_NODATA | OBJ_MULTIPLE, get_best_metric_cb, NULL, &best);
	ao2_lock(data);
	if (best) {
		/* Ring just the best channel */
		ast_debug(1, "Next is '%s' with metric %d\n", best->member->interface, best->metric);
		data->rrpos = best->metric % 1000;
		ao2_ref(best, -1);
	} else {
		/* Just increment rrpos */
		if (data->wrapped) {
			/* No more channels, start over */
			data->rrpos = 0;
		} else {
			/* Prioritize next entry */
			data->rrpos++;
		}
	}
	data->wrapped = 0;
	ao2_unlock(data);

	return 0;
}

/*! \brief Search for best metric and add to Linear queue */
static int store_next_lin(struct queue_ent *qe)
{
	struct callattempt *best = NULL;

	ao2_callback_data(qe->attempts, OBJ_NODATA | OBJ_MULTIPLE, get_best_metric_cb, NULL, &best);

	if (best) {
		/* Ring just the best channel */
		ast_debug(1, "Next is '%s' with metric %d\n", best->member->interface, best->metric);
		qe->linpos = best->metric % 1000;
		ao2_ref(best, -1);
	} else {
		/* Just increment rrpos */
		if (qe->linwrapped) {
			/* No more channels, start over */
			qe->linpos = 0;
		} else {
			/* Prioritize next entry */
			qe->linpos++;
		}
	}
	qe->linwrapped = 0;

	return 0;
}

/*! \brief Playback announcement to queued members if period has elapsed */
static int say_periodic_announcement(struct queue_ent *qe, int ringing)
{
	int res = 0;
	struct timeval now;

	/* Get the current time */
	now = ast_tvnow();

	/* Check to see if it is time to announce */
	if (ast_tvdiff_sec(now, qe->last_pannounce_time) < qe->parent->periodicannouncefrequency) {
		return 0;
	}

	/* Stop the music on hold so we can play our own file */
	if (ringing)
		ast_indicate(qe->chan,-1);
	else
		ast_moh_stop(qe->chan);

	ast_verb(3, "Playing periodic announcement\n");
	
	if (qe->parent->randomperiodicannounce && qe->parent->numperiodicannounce) {
		qe->last_periodic_announce_sound = ((unsigned long) ast_random()) % qe->parent->numperiodicannounce;
	} else if (qe->last_periodic_announce_sound >= qe->parent->numperiodicannounce || 
		ast_str_strlen(qe->parent->sound_periodicannounce[qe->last_periodic_announce_sound]) == 0) {
		qe->last_periodic_announce_sound = 0;
	}
	
	/* play the announcement */
	res = play_file(qe->chan, ast_str_buffer(qe->parent->sound_periodicannounce[qe->last_periodic_announce_sound]));

	if (res > 0 && !valid_exit(qe, res))
		res = 0;

	/* Resume Music on Hold if the caller is going to stay in the queue */
	if (!res) {
		if (ringing) {
			ast_indicate(qe->chan, AST_CONTROL_RINGING);
		} else {
			ast_moh_start(qe->chan, qe->parent->moh, NULL);
		}
	}

	/* update last_pannounce_time */
	if (qe->parent->relativeperiodicannounce) {
		qe->last_pannounce_time = ast_tvnow();
	} else {
		qe->last_pannounce_time = now;
	}

	/* Update the current periodic announcement to the next announcement */
	if (!qe->parent->randomperiodicannounce) {
		qe->last_periodic_announce_sound++;
	}

	return res;
}

/*! \brief Record that a caller gave up on waiting in queue */
static void record_abandoned(struct queue_ent *qe)
{
	set_queue_variables(qe->parent, qe->chan);
	manager_event(EVENT_FLAG_AGENT, "QueueCallerAbandon",
		"Queue: %s\r\n"
		"Uniqueid: %s\r\n"
		"Position: %d\r\n"
		"OriginalPosition: %d\r\n"
		"HoldTime: %d\r\n",
		qe->parent->name, qe->chan->uniqueid, qe->pos, qe->opos, (int)ast_tvdiff_sec(ast_tvnow(), qe->start));

	ao2_lock(qe->parent->data);
	qe->parent->data->callsabandoned++;
	ao2_unlock(qe->parent->data);
}

/*! \brief RNA == Ring No Answer. Common code that is executed when we try a queue member and they don't answer. */
static void rna(int rnatime, struct queue_ent *qe, struct callattempt *call, int pause)
{
	ast_verb(3, "Nobody picked up in %d ms\n", rnatime);

	/* Stop ringing, and resume MOH if specified */
	if (qe->ring_when_ringing) {
		ast_indicate(qe->chan, -1);
		ast_moh_start(qe->chan, qe->parent->moh, NULL);
	}

	ao2_lock(call->member);
	if (qe->parent->eventwhencalled) {
		char vars[2048];

		manager_event(EVENT_FLAG_AGENT, "AgentRingNoAnswer",
						"Queue: %s\r\n"
						"Uniqueid: %s\r\n"
						"Channel: %s\r\n"
						"Member: %s\r\n"
						"MemberName: %s\r\n"
						"Ringtime: %d\r\n"
						"%s",
						qe->parent->name,
						qe->chan->uniqueid,
						qe->chan->name,
						call->member->interface,
						call->member->membername,
						rnatime,
						qe->parent->eventwhencalled == QUEUE_EVENT_VARIABLES ? vars2manager(qe->chan, vars, sizeof(vars)) : "");
	}
	ast_queue_log(qe->parent->name, qe->chan->uniqueid, call->member->membername, "RINGNOANSWER", "%d", rnatime);
	ao2_unlock(call->member);

	if (qe->parent->autopause != QUEUE_AUTOPAUSE_OFF && pause) {
		if ((qe->parent->autopausedelay > 0) && !ast_tvzero(call->member->lastcall) &&
		    (ast_tvdiff_sec(ast_tvnow(), call->member->lastcall) < qe->parent->autopausedelay)) {
			return;
		}
		if (qe->parent->autopause == QUEUE_AUTOPAUSE_ON) {
			ao2_lock(call->member);
			if (!(do_set_member_penalty_paused(qe->parent, call->member, 1, 1, "Auto-Pause"))) {
				ast_verb(3, "Auto-Pausing Queue Member %s in queue %s since they failed to answer.\n",
							call->member->interface, qe->parent->name);
			} else {
				ast_verb(3, "Failed to pause Queue Member %s in queue %s!\n", call->member->interface, qe->parent->name);
			}
			ao2_unlock(call->member);
		} else {
			/* If queue autopause is mode all, just don't send any queue to stop.
			* the function will stop in all queues */
			if (!set_member_paused("", call->member->interface, "Auto-Pause", 1)) {
				ast_verb(3, "Auto-Pausing Queue Member %s in all queues since they failed to answer on queue %s.\n",
						call->member->interface, qe->parent->name);
			} else {
					ast_verb(3, "Failed to pause Queue Member %s in all queues!\n", call->member->interface);
			}
		}
	}
	return;
}

#define AST_MAX_WATCHERS 256
/*!
 * \brief Wait for a member to answer the call
 *
 * \param[in] qe the queue_ent corresponding to the caller in the queue
 * \param[in] outgoing the list of callattempts. Relevant ones will have their chan and stillgoing parameters non-zero
 * \param[in] to the amount of time (in milliseconds) to wait for a response
 * \param[out] digit if a user presses a digit to exit the queue, this is the digit the caller pressed
 * \param[in] prebusies number of busy members calculated prior to calling wait_for_answer
 * \param[in] caller_disconnect if the 'H' option is used when calling Queue(), this is used to detect if the caller pressed * to disconnect the call
 * \param[in] forwardsallowed used to detect if we should allow call forwarding, based on the 'i' option to Queue()
 * \param[in] update_connectedline Allow connected line and redirecting updates to pass through.
 *
 * \todo eventually all call forward logic should be intergerated into and replaced by ast_call_forward()
 */
static struct callattempt *wait_for_answer(struct queue_ent *qe, struct callattempt *outgoing, int *to, char *digit, int prebusies, int caller_disconnect, int forwardsallowed, int update_connectedline)
{
	const char *queue = qe->parent->name;
	struct callattempt *o;
	int res;
	int status;
	int numbusies = prebusies;
	int numnochan = 0;
	int stillgoing = 0;
	int orig = *to;
	struct ast_frame *f;
	struct callattempt *peer = NULL;
	struct ast_channel *winner;
	struct ast_channel *in = qe->chan;
	long starttime = 0;
	long endtime = 0;
	struct ao2_iterator aiter, *calls;
#ifdef HAVE_EPOLL
	struct callattempt *epollo;
#endif
	struct ast_party_connected_line connected_caller;
	char *inchan_name;

	ast_party_connected_line_init(&connected_caller);

	ast_channel_lock(qe->chan);
	inchan_name = ast_strdupa(qe->chan->name);
	ast_channel_unlock(qe->chan);

	starttime = (long) time(NULL);
#ifdef HAVE_EPOLL
	aiter = ao2_iterator_init(qe->attempts, 0);
	while ((epollo = ao2_iterator_next(&aiter))) {
		if (epollo->chan) {
			ast_poll_channel_add(in, epollo->chan);
		}
		ao2_ref(epollo, -1);
	}
	ao2_iterator_destroy(&aiter);
#endif

	while (*to && !peer) {
		int numlines, retry, pos = 1;
		struct ast_channel *watchers[AST_MAX_WATCHERS];
		watchers[0] = in;

		for (retry = 0; retry < 2; retry++) {
			numlines = 0;
			aiter = ao2_iterator_init(qe->attempts, 0);
			while ((o = ao2_iterator_next(&aiter))) {
				if (o->stillgoing) {	/* Keep track of important channels */
					stillgoing = 1;
					if (o->chan && !o->watching && (pos < AST_MAX_WATCHERS)) {
						watchers[pos++] = o->chan;
						o->watching = 1;
					}
				}
				numlines++;
				ao2_ref(o, -1);
			}
			ao2_iterator_destroy(&aiter);
			if (pos > 1 /* found */ || !stillgoing /* nobody listening */ ||
				(qe->parent->strategy != QUEUE_STRATEGY_RINGALL) /* ring would not be delivered */) {
				break;
			}
			/* On "ringall" strategy we only move to the next penalty level
			   when *all* ringing phones are done in the current penalty level */
			ring_one(qe, &numbusies);
			/* and retry... */
		}
		if (pos == 1 /* not found */) {
			if (numlines == (numbusies + numnochan)) {
				ast_debug(1, "Everyone is busy at this time\n");
			} else {
				ast_debug(3, "No one is answering queue '%s' (%d numlines / %d busies / %d failed channels)\n", queue, numlines, numbusies, numnochan);
			}
			*to = 0;
			return NULL;
		}

		/* Poll for events from both the incoming channel as well as any outgoing channels */
		winner = ast_waitfor_n(watchers, pos, to);

		/* Service all of the outgoing channels */
		calls = ao2_find(qe->attempts, NULL, OBJ_MULTIPLE);
		while (calls && (o = ao2_iterator_next(calls))) {
			/* We go with a static buffer here instead of using ast_strdupa. Using
			 * ast_strdupa in a loop like this one can cause a stack overflow
			 */
			char ochan_name[AST_CHANNEL_NAME];

			/* i need to be re added to the watchers */
			if (!o->watching) {
				ao2_ref(o, -1);
				continue;
			} else {
				o->watching = 0;
			}

			if (o->chan) {
				ast_channel_lock(o->chan);
				ast_copy_string(ochan_name, o->chan->name, sizeof(ochan_name));
				ast_channel_unlock(o->chan);
			}
			if (o->stillgoing && o->chan &&  (o->chan->_state == AST_STATE_UP)) {
				if (!peer) {
					ast_verb(3, "%s answered %s\n", ochan_name, inchan_name);
					if (update_connectedline) {
						if (o->pending_connected_update) {
							if (ast_channel_connected_line_macro(o->chan, in, &o->connected, 1, 0)) {
								ast_channel_update_connected_line(in, &o->connected, NULL);
							}
						} else if (!o->dial_callerid_absent) {
							ast_channel_lock(o->chan);
							ast_connected_line_copy_from_caller(&connected_caller, &o->chan->caller);
							ast_channel_unlock(o->chan);
							connected_caller.source = AST_CONNECTED_LINE_UPDATE_SOURCE_ANSWER;
							ast_channel_update_connected_line(in, &connected_caller, NULL);
							ast_party_connected_line_free(&connected_caller);
						}
					}
					if (o->aoc_s_rate_list) {
						size_t encoded_size;
						struct ast_aoc_encoded *encoded;
						if ((encoded = ast_aoc_encode(o->aoc_s_rate_list, &encoded_size, o->chan))) {
							ast_indicate_data(in, AST_CONTROL_AOC, encoded, encoded_size);
							ast_aoc_destroy_encoded(encoded);
						}
					}
					if (!peer || (peer && (peer != o))) {
						if (peer) {
							ao2_ref(peer, -1);
						}
						ao2_ref(o, 1);
						peer = o;
					}
				}
			} else if (o->chan && (o->chan == winner)) {
				if (!ast_strlen_zero(o->chan->call_forward) && !forwardsallowed) {
					ast_verb(3, "Forwarding %s to '%s' prevented.\n", inchan_name, o->chan->call_forward);
					numnochan++;
					do_hang(o);
					winner = NULL;
					ao2_ref(o, -1);
					continue;
				} else if (!ast_strlen_zero(o->chan->call_forward)) {
					struct ast_channel *original = o->chan;
					char tmpchan[256];
					char *stuff;
					char *tech;

					ast_copy_string(tmpchan, o->chan->call_forward, sizeof(tmpchan));
					if ((stuff = strchr(tmpchan, '/'))) {
						*stuff++ = '\0';
						tech = tmpchan;
					} else {
						snprintf(tmpchan, sizeof(tmpchan), "%s@%s", o->chan->call_forward, o->chan->context);
						stuff = tmpchan;
						tech = "Local";
					}

					ast_cel_report_event(in, AST_CEL_FORWARD, NULL, o->chan->call_forward, NULL);

					/* Before processing channel, go ahead and check for forwarding */
					ast_verb(3, "Now forwarding %s to '%s/%s' (thanks to %s)\n", inchan_name, tech, stuff, ochan_name);
					/* Setup parameters */
					o->chan = ast_request(tech, in->nativeformats, in, stuff, &status);
					if (!o->chan) {
						ast_log(LOG_NOTICE,
							"Forwarding failed to create channel to dial '%s/%s'\n",
							tech, stuff);
						o->stillgoing = 0;
						numnochan++;
					} else {
						struct ast_party_redirecting redirecting;

						ast_channel_lock_both(o->chan, in);
						ast_channel_inherit_variables(in, o->chan);
						ast_channel_datastore_inherit(in, o->chan);

						ast_string_field_set(o->chan, accountcode, in->accountcode);

						ast_channel_set_redirecting(o->chan, &original->redirecting, NULL);
						if (!o->chan->redirecting.from.number.valid
							|| ast_strlen_zero(o->chan->redirecting.from.number.str)) {
							/*
							 * The call was not previously redirected so it is
							 * now redirected from this number.
							 */
							ast_party_number_free(&o->chan->redirecting.from.number);
							ast_party_number_init(&o->chan->redirecting.from.number);
							o->chan->redirecting.from.number.valid = 1;
							o->chan->redirecting.from.number.str =
								ast_strdup(S_OR(in->macroexten, in->exten));
						}

						o->chan->dialed.transit_network_select = in->dialed.transit_network_select;

						ast_party_caller_copy(&o->chan->caller, &in->caller);
						ast_party_connected_line_copy(&o->chan->connected, &original->connected);

						/*
						 * We must unlock o->chan before calling
						 * ast_channel_redirecting_macro, because we put o->chan into
						 * autoservice there.  That is pretty much a guaranteed
						 * deadlock.  This is why the handling of o->chan's lock may
						 * seem a bit unusual here.
						 */
						ast_party_redirecting_init(&redirecting);
						ast_party_redirecting_copy(&redirecting, &o->chan->redirecting);
						ast_channel_unlock(o->chan);
						res = ast_channel_redirecting_macro(o->chan, in, &redirecting, 1, 0);
						if (res) {
							ast_channel_update_redirecting(in, &redirecting, NULL);
						}
						ast_party_redirecting_free(&redirecting);
						ast_channel_unlock(in);

						update_connectedline = 1;

						if (ast_call(o->chan, stuff, 0)) {
							ast_log(LOG_NOTICE, "Forwarding failed to dial '%s/%s'\n",
								tech, stuff);
							do_hang(o);
							numnochan++;
						}
					}
					/* Hangup the original channel now, in case we needed it */
					ast_hangup(winner);
					ao2_ref(o, -1);
					continue;
				}
				if (!(f = ast_read(winner))) {
					endtime = (long) time(NULL) - starttime;
					rna(endtime * 1000, qe, o, 1);
					do_hang(o);
					if (qe->parent->strategy != QUEUE_STRATEGY_RINGALL) {
						if (qe->parent->timeoutrestart) {
							*to = orig;
						}
						if (*to > 500) {
							ring_one(qe, &numbusies);
							starttime = (long) time(NULL);
						}
					}
					ao2_ref(o, -1);
					continue;
				} else if (f->frametype != AST_FRAME_CONTROL) {
					ast_frfree(f);
					ao2_ref(o, -1);
					continue;
				}

				switch (f->subclass.integer) {
				case AST_CONTROL_ANSWER:
					/* This is our guy if someone answered. */
					if (!peer) {
						ast_verb(3, "%s answered %s\n", ochan_name, inchan_name);
						if (update_connectedline) {
							if (o->pending_connected_update) {
								if (ast_channel_connected_line_macro(o->chan, in, &o->connected, 1, 0)) {
									ast_channel_update_connected_line(in, &o->connected, NULL);
								}
							} else if (!o->dial_callerid_absent) {
								ast_channel_lock(o->chan);
								ast_connected_line_copy_from_caller(&connected_caller, &o->chan->caller);
								ast_channel_unlock(o->chan);
								connected_caller.source = AST_CONNECTED_LINE_UPDATE_SOURCE_ANSWER;
								ast_channel_update_connected_line(in, &connected_caller, NULL);
								ast_party_connected_line_free(&connected_caller);
							}
						}
						if (o->aoc_s_rate_list) {
							size_t encoded_size;
							struct ast_aoc_encoded *encoded;
							if ((encoded = ast_aoc_encode(o->aoc_s_rate_list, &encoded_size, o->chan))) {
								ast_indicate_data(in, AST_CONTROL_AOC, encoded, encoded_size);
								ast_aoc_destroy_encoded(encoded);
							}
						}
						if (!peer || (peer && (peer != o))) {
							if (peer) {
								ao2_ref(peer, -1);
							}
							ao2_ref(o, 1);
							peer = o;
						}
					}
					break;
				case AST_CONTROL_BUSY:
					ast_verb(3, "%s is busy\n", ochan_name);
					if (in->cdr)
						ast_cdr_busy(in->cdr);
					do_hang(o);
					endtime = (long) time(NULL);
					endtime -= starttime;
					rna(endtime * 1000, qe, o, qe->parent->autopausebusy);
					if (qe->parent->strategy != QUEUE_STRATEGY_RINGALL) {
						if (qe->parent->timeoutrestart)
							*to = orig;
						/* Have enough time for a queue member to answer? */
						if (*to > 500) {
							ring_one(qe, &numbusies);
							starttime = (long) time(NULL);
						}
					}
					numbusies++;
					break;
				case AST_CONTROL_CONGESTION:
					ast_verb(3, "%s is circuit-busy\n", ochan_name);
					if (in->cdr)
						ast_cdr_busy(in->cdr);
					endtime = (long) time(NULL);
					endtime -= starttime;
					rna(endtime * 1000, qe, o, qe->parent->autopauseunavail);
					do_hang(o);
					if (qe->parent->strategy != QUEUE_STRATEGY_RINGALL) {
						if (qe->parent->timeoutrestart)
							*to = orig;
						if (*to > 500) {
							ring_one(qe, &numbusies);
							starttime = (long) time(NULL);
						}
					}
					numbusies++;
					break;
				case AST_CONTROL_RINGING:
					ast_verb(3, "%s is ringing\n", ochan_name);

					/* Start ring indication when the channel is ringing, if specified */
					if (qe->ring_when_ringing) {
						ast_moh_stop(qe->chan);
						ast_indicate(qe->chan, AST_CONTROL_RINGING);
					}
					break;
				case AST_CONTROL_OFFHOOK:
					/* Ignore going off hook */
					break;
				case AST_CONTROL_CONNECTED_LINE:
					if (!update_connectedline) {
						ast_verb(3, "Connected line update to %s prevented.\n", inchan_name);
					} else if (qe->parent->strategy == QUEUE_STRATEGY_RINGALL) {
						struct ast_party_connected_line connected;
						ast_verb(3, "%s connected line has changed. Saving it until answer for %s\n", ochan_name, inchan_name);
						ast_party_connected_line_set_init(&connected, &o->connected);
						ast_connected_line_parse_data(f->data.ptr, f->datalen, &connected);
						ast_party_connected_line_set(&o->connected, &connected, NULL);
						ast_party_connected_line_free(&connected);
						o->pending_connected_update = 1;
					} else {
						if (ast_channel_connected_line_macro(o->chan, in, f, 1, 1)) {
							ast_indicate_data(in, AST_CONTROL_CONNECTED_LINE, f->data.ptr, f->datalen);
						}
					}
					break;
				case AST_CONTROL_AOC:
					{
						struct ast_aoc_decoded *decoded = ast_aoc_decode(f->data.ptr, f->datalen, o->chan);
						if (decoded && (ast_aoc_get_msg_type(decoded) == AST_AOC_S)) {
							ast_aoc_destroy_decoded(o->aoc_s_rate_list);
							o->aoc_s_rate_list = decoded;
						} else {
							ast_aoc_destroy_decoded(decoded);
						}
					}
					break;
				case AST_CONTROL_REDIRECTING:
					if (!update_connectedline) {
						ast_verb(3, "Redirecting update to %s prevented\n", inchan_name);
					} else if (qe->parent->strategy != QUEUE_STRATEGY_RINGALL) {
						ast_verb(3, "%s redirecting info has changed, passing it to %s\n", ochan_name, inchan_name);
						if (ast_channel_redirecting_macro(o->chan, in, f, 1, 1)) {
							ast_indicate_data(in, AST_CONTROL_REDIRECTING, f->data.ptr, f->datalen);
						}
					}
					break;
				default:
					ast_debug(1, "Dunno what to do with control type %d\n", f->subclass.integer);
					break;
				}
				ast_frfree(f);
			}
			ao2_ref(o, -1);
		}
		if (calls) {
			ao2_iterator_destroy(calls);
		}

		/* If we received an event from the caller, deal with it. */
		if (winner == in) {
			f = ast_read(in);
			if (!f || ((f->frametype == AST_FRAME_CONTROL) && (f->subclass.integer == AST_CONTROL_HANGUP))) {
				/* Got hung up */
				*to = -1;
				if (f) {
					if (f->data.uint32) {
						in->hangupcause = f->data.uint32;
					}
					ast_frfree(f);
				}
				if (peer) {
					ao2_ref(peer, -1);
				}
				return NULL;
			}
			if ((f->frametype == AST_FRAME_DTMF) && caller_disconnect && (f->subclass.integer == '*')) {
				ast_verb(3, "User hit %c to disconnect call.\n", f->subclass.integer);
				*to = 0;
				ast_frfree(f);
				if (peer) {
					ao2_ref(peer, -1);
				}
				return NULL;
			}
			if ((f->frametype == AST_FRAME_DTMF) && valid_exit(qe, f->subclass.integer)) {
				ast_verb(3, "User pressed digit: %c\n", f->subclass.integer);
				*to = 0;
				*digit = f->subclass.integer;
				ast_frfree(f);
				if (peer) {
					ao2_ref(peer, -1);
				}
				return NULL;
			}
			ast_frfree(f);
		}
		if (!*to) {
			calls = ao2_find(qe->attempts, NULL, OBJ_MULTIPLE);
			while (calls && (o = ao2_iterator_next(calls))) {
				rna(orig, qe, o, 1);
				ao2_ref(o, -1);
			}
			if (calls) {
				ao2_iterator_destroy(calls);
			}
		}
	}

#ifdef HAVE_EPOLL
	aiter = ao2_iterator_init(qe->attempts, 0);
	while ((epollo = ao2_iterator_next(&aiter))) {
		if (epollo->chan) {
			ast_poll_channel_del(in, epollo->chan);
		}
		ao2_ref(epollo, -1);
	}
	ao2_iterator_destroy(&aiter);
#endif

	return peer;
}

/*! 
 * \brief Check if we should start attempting to call queue members.
 *
 * A simple process, really. Count the number of members who are available
 * to take our call and then see if we are in a position in the queue at
 * which a member could accept our call.
 *
 * \param[in] qe The caller who wants to know if it is his turn
 * \retval 0 It is not our turn
 * \retval 1 It is our turn
 */
static int is_our_turn(struct queue_ent *qe)
{
	struct queue_ent *ch;
	int res;
	int avl;
	int idx = 0;

	/* How many members are available to be served? */
	avl = num_available_members(qe->parent);

	ast_debug(1, "There %s %d available %s.\n", avl != 1 ? "are" : "is", avl, avl != 1 ? "members" : "member");

	AST_LIST_LOCK(qe->parent->data->head);
	ch = AST_LIST_FIRST(qe->parent->data->head);
	while (ch && (idx < avl) && (ch != qe)) {
		if (!ch->pending) {
			idx++;
		}
		ch = AST_LIST_NEXT(ch, next);
	}

	/* If the queue entry is within avl [the number of available members] calls from the top ...
	 * Autofill and position check added to support autofill=no (as only calls
	 * from the front of the queue are valid when autofill is disabled)
	 */
	if (ch && (idx < avl) && (qe->parent->autofill || qe->pos == 1)) {
		ast_debug(1, "It's our turn (%s).\n", qe->chan->name);
		res = 1;
	} else {
		ast_debug(1, "It's not our turn (%s).\n", qe->chan->name);
		res = 0;
	}
	AST_LIST_UNLOCK(qe->parent->data->head);

	return res;
}

/*!
 * \brief update rules for queues
 *
 * Calculate min/max penalties making sure if relative they stay within bounds.
 * Update queues penalty and set dialplan vars, goto next list entry.
*/
static void update_qe_rule(struct queue_ent *qe)
{
	int max_penalty = qe->pr->max_relative ? qe->max_penalty + qe->pr->max_value : qe->pr->max_value;
	int min_penalty = qe->pr->min_relative ? qe->min_penalty + qe->pr->min_value : qe->pr->min_value;
	char max_penalty_str[20], min_penalty_str[20];
	int next = qe->pr->time;

	/* a relative change to the penalty could put it below 0 */
	if (max_penalty < 0)
		max_penalty = 0;
	if (min_penalty < 0)
		min_penalty = 0;
	if (min_penalty > max_penalty)
		min_penalty = max_penalty;
	snprintf(max_penalty_str, sizeof(max_penalty_str), "%d", max_penalty);
	snprintf(min_penalty_str, sizeof(min_penalty_str), "%d", min_penalty);
	pbx_builtin_setvar_helper(qe->chan, "QUEUE_MAX_PENALTY", max_penalty_str);
	pbx_builtin_setvar_helper(qe->chan, "QUEUE_MIN_PENALTY", min_penalty_str);
	qe->max_penalty = max_penalty;
	qe->min_penalty = min_penalty;
	ast_debug(3, "Setting max penalty to %d and min penalty to %d for caller %s since %d seconds have elapsed\n", qe->max_penalty, qe->min_penalty, qe->chan->name, qe->pr->time);
	ao2_ref(qe->pr, -1);
	qe->pr = NULL;
	ao2_callback_data(qe->rules->rules, OBJ_NODATA | OBJ_MULTIPLE, get_best_rule_cb, &next, &qe->pr);
}

/*! \brief The waiting areas for callers who are not actively calling members
 *
 * This function is one large loop. This function will return if a caller
 * either exits the queue or it becomes that caller's turn to attempt calling
 * queue members. Inside the loop, we service the caller with periodic announcements,
 * holdtime announcements, etc. as configured in queues.conf
 *
 * \retval  0 if the caller's turn has arrived
 * \retval -1 if the caller should exit the queue.
 */
static int wait_our_turn(struct queue_ent *qe, int ringing, enum queue_result *reason)
{
	int res = 0;

	/* This is the holding pen for callers 2 through maxlen */
	for (;;) {

		if (is_our_turn(qe))
			break;

		/* If we have timed out, break out */
		if (!ast_tvzero(qe->expire) && (ast_tvcmp(ast_tvnow(), qe->expire) >= 0)) {
			*reason = QUEUE_TIMEOUT;
			break;
		}

		if (get_member_status(qe, 0)) {
			*reason = QUEUE_LEAVEEMPTY;
			ast_queue_log(qe->parent->name, qe->chan->uniqueid, "NONE", "EXITEMPTY", "%d|%d|%ld", qe->pos, qe->opos, (long)ast_tvdiff_sec(ast_tvnow(), qe->start));
			leave_queue(qe);
			break;
		}

		/* Make a position announcement, if enabled */
		if (qe->parent->announcefrequency &&
			(res = say_position(qe,ringing))) {
			break;
		}

		/* If we have timed out, break out */
		if (!ast_tvzero(qe->expire) && (ast_tvcmp(ast_tvnow(), qe->expire) >= 0)) {
			*reason = QUEUE_TIMEOUT;
			break;
		}

		/* Make a periodic announcement, if enabled */
		if (qe->parent->periodicannouncefrequency &&
			(res = say_periodic_announcement(qe,ringing)))
			break;

		/* see if we need to move to the next penalty level for this queue */
		while (qe->pr && (ast_tvdiff_sec(ast_tvnow(), qe->start) >= qe->pr->time)) {
			update_qe_rule(qe);
		}

		/* If we have timed out, break out */
		if (!ast_tvzero(qe->expire) && (ast_tvcmp(ast_tvnow(), qe->expire) >= 0)) {
			*reason = QUEUE_TIMEOUT;
			break;
		}

		/* Wait a second before checking again */
		if ((res = ast_waitfordigit(qe->chan, RECHECK * 1000))) {
			if (res > 0 && !valid_exit(qe, res)) {
				res = 0;
			} else {
				break;
			}
		}

		/* If we have timed out, break out */
		if (!ast_tvzero(qe->expire) && (ast_tvcmp(ast_tvnow(), qe->expire) >= 0)) {
			*reason = QUEUE_TIMEOUT;
			break;
		}
	}

	return res;
}

/*!
 * \brief update the queue status
 * \retval Always 0
*/
static int update_queue(struct call_queue *q, struct member *member, int callcompletedinsl, int newtalktime)
{
	int oldtalktime;

	struct member *mem;
	struct queue_data *qtmp;
	struct ao2_iterator queue_iter;

	ao2_lock(q->data);
	q->data->callscompleted++;
	if (callcompletedinsl) {
		q->data->callscompletedinsl++;
	}
	/* Calculate talktime using the same exponential average as holdtime code*/
	oldtalktime = q->data->talktime;
	q->data->talktime = (((oldtalktime << 2) - oldtalktime) + newtalktime) >> 2;
	ao2_unlock(q->data);

	if (shared_lastcall) {
		queue_iter = ao2_iterator_init(qdata, 0);
		while ((qtmp = ao2_t_iterator_next(&queue_iter, "Iterate through queues"))) {
			if ((mem = ao2_find(qtmp->members, member, OBJ_POINTER))) {
				ao2_lock(mem);
				mem->lastcall = ast_tvnow();
				mem->calls++;
				mem->lastwrapup = q->wrapuptime;
				ao2_unlock(mem);
				ao2_ref(mem, -1);
			}
			ao2_t_ref(qtmp, -1, "Done with iterator");
		}
		ao2_iterator_destroy(&queue_iter);
	} else {
		ao2_lock(member);
		member->lastcall = ast_tvnow();
		member->calls++;
		member->lastwrapup = q->wrapuptime;
		ao2_unlock(member);
	}

	return 0;
}

/*! \brief Create a new call attempt for the queue from member
 *
 * A numeric metric is given to each member depending on the ring strategy used
 * by the queue. Members with lower metrics will be called before members with
 * higher metrics
 * \retval null if metric cannot be allocated
 * \retval new callattempt otherwise
 */
static struct callattempt *new_attempt(struct queue_ent *qe, struct member *mem, int pos)
{
	int metric;
	struct callattempt *tmp;
	struct call_queue *q = qe->parent;
	/* disregarding penalty on too few members? */
	int membercount = ao2_container_count(q->data->members);
	unsigned char usepenalty = (membercount <= q->penaltymemberslimit) ? 0 : 1;

	ao2_lock(mem);
	if (usepenalty) {
		if ((qe->max_penalty && (mem->penalty > qe->max_penalty)) ||
		    (qe->min_penalty && (mem->penalty < qe->min_penalty))) {
			ao2_unlock(mem);
			return NULL;
		}
	} else {
		ast_debug(1, "Disregarding penalty, %d members and %d in penaltymemberslimit.\n",
			  membercount, q->penaltymemberslimit);
	}

	switch (q->strategy) {
	case QUEUE_STRATEGY_RINGALL:
		/* Everyone equal, except for penalty */
		metric = mem->penalty * 1000000 * usepenalty;
		break;
	case QUEUE_STRATEGY_LINEAR:
		if (pos < qe->linpos) {
			metric = 1000 + pos;
		} else {
			if (pos > qe->linpos)
				/* Indicate there is another priority */
				qe->linwrapped = 1;
			metric = pos;
		}
		metric += mem->penalty * 1000000 * usepenalty;
		break;
	case QUEUE_STRATEGY_RRORDERED:
	case QUEUE_STRATEGY_RRMEMORY:
		ao2_lock(q->data);
		if (pos < q->data->rrpos) {
			metric = 1000 + pos;
		} else {
			if (pos > q->data->rrpos)
				/* Indicate there is another priority */
				q->data->wrapped = 1;
			metric = pos;
		}
		ao2_unlock(q->data);
		metric += mem->penalty * 1000000 * usepenalty;
		break;
	case QUEUE_STRATEGY_RANDOM:
		metric = ast_random() % 1000;
		metric += mem->penalty * 1000000 * usepenalty;
		break;
	case QUEUE_STRATEGY_WRANDOM:
		metric = ast_random() % ((1 + mem->penalty) * 1000);
		break;
	case QUEUE_STRATEGY_FEWESTCALLS:
		metric = mem->calls;
		metric += mem->penalty * 1000000 * usepenalty;
		break;
	case QUEUE_STRATEGY_LEASTRECENT:
		if (ast_tvzero(mem->lastcall)) {
			metric = 0;
		} else {
			metric = 1000000 - ast_tvdiff_sec(ast_tvnow(), mem->lastcall);
		}
		metric += mem->penalty * 1000000 * usepenalty;
		break;
	default:
		ast_log(LOG_WARNING, "Can't calculate metric for unknown strategy %d\n", q->strategy);
		metric = -1;
		break;
	}
	ao2_unlock(mem);

	if ((metric < 0) || (!(tmp = ao2_alloc(sizeof(*tmp), callattempt_free)))) {
		return NULL;
	}

	tmp->stillgoing = 1;
	tmp->watching = 0;
	tmp->member = mem;/* Place the reference for mem into callattempt. */
	tmp->dial_callerid_absent = 0;
	tmp->pending_connected_update =0;
	tmp->metric = metric;

	return tmp;
}

enum agent_complete_reason {
	CALLER,
	AGENT,
	TRANSFER
};

/*! \brief Send out AMI message with member call completion status information */
static void send_agent_complete(const struct queue_ent *qe, const char *queuename,
	const struct ast_channel *peer, struct member *member, struct timeval callstart,
	char *vars, size_t vars_len, enum agent_complete_reason rsn)
{
	const char *reason = NULL;	/* silence dumb compilers */

	if (!qe->parent->eventwhencalled)
		return;

	switch (rsn) {
	case CALLER:
		reason = "caller";
		break;
	case AGENT:
		reason = "agent";
		break;
	case TRANSFER:
		reason = "transfer";
		break;
	}

	manager_event(EVENT_FLAG_AGENT, "AgentComplete",
		"Queue: %s\r\n"
		"Uniqueid: %s\r\n"
		"Channel: %s\r\n"
		"Member: %s\r\n"
		"MemberName: %s\r\n"
		"HoldTime: %ld\r\n"
		"TalkTime: %ld\r\n"
		"Reason: %s\r\n"
		"%s",
		queuename, qe->chan->uniqueid, peer->name, member->interface, member->membername,
		(long)ast_tvdiff_sec(callstart, qe->start), (long)ast_tvdiff_sec(ast_tvnow(), callstart), reason,
		qe->parent->eventwhencalled == QUEUE_EVENT_VARIABLES ? vars2manager(qe->chan, vars, vars_len) : "");
}

struct queue_transfer_ds {
	struct queue_ent *qe;
	struct member *member;
	struct timeval starttime;
	int callcompletedinsl;
};

static void queue_transfer_destroy(void *data)
{
	struct queue_transfer_ds *qtds = data;
	ast_free(qtds);
}

/*! \brief a datastore used to help correctly log attended transfers of queue callers
 */
static const struct ast_datastore_info queue_transfer_info = {
	.type = "queue_transfer",
	.chan_fixup = queue_transfer_fixup,
	.destroy = queue_transfer_destroy,
};

/*! \brief Log an attended transfer when a queue caller channel is masqueraded
 *
 * When a caller is masqueraded, we want to log a transfer. Fixup time is the closest we can come to when
 * the actual transfer occurs. This happens during the masquerade after datastores are moved from old_chan
 * to new_chan. This is why new_chan is referenced for exten, context, and datastore information.
 *
 * At the end of this, we want to remove the datastore so that this fixup function is not called on any
 * future masquerades of the caller during the current call.
 */
static void queue_transfer_fixup(void *data, struct ast_channel *old_chan, struct ast_channel *new_chan)
{
	struct queue_transfer_ds *qtds = data;
	struct queue_ent *qe = qtds->qe;
	struct member *member = qtds->member;
	struct timeval callstart = qtds->starttime;
	int callcompletedinsl = qtds->callcompletedinsl;
	struct ast_datastore *datastore;

	ao2_lock(member);
	ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "TRANSFER", "%s|%s|%ld|%ld|%d",
				new_chan->exten, new_chan->context, (long)ast_tvdiff_sec(callstart, qe->start),
				(long)ast_tvdiff_sec(ast_tvnow(), callstart), qe->opos);

	ao2_unlock(member);

	update_queue(qe->parent, member, callcompletedinsl, ast_tvdiff_sec(ast_tvnow(), callstart));

	/* No need to lock the channels because they are already locked in ast_do_masquerade */
	if ((datastore = ast_channel_datastore_find(old_chan, &queue_transfer_info, NULL))) {
		ast_channel_datastore_remove(old_chan, datastore);
	} else {
		ast_log(LOG_WARNING, "Can't find the queue_transfer datastore.\n");
	}
}

/*! \brief mechanism to tell if a queue caller was atxferred by a queue member.
 *
 * When a caller is atxferred, then the queue_transfer_info datastore
 * is removed from the channel. If it's still there after the bridge is
 * broken, then the caller was not atxferred.
 *
 * \note Only call this with chan locked
 */
static int attended_transfer_occurred(struct ast_channel *chan)
{
	return ast_channel_datastore_find(chan, &queue_transfer_info, NULL) ? 0 : 1;
}

/*! \brief create a datastore for storing relevant info to log attended transfers in the queue_log
 */
static struct ast_datastore *setup_transfer_datastore(struct queue_ent *qe, struct member *member, struct timeval starttime, int callcompletedinsl)
{
	struct ast_datastore *ds;
	struct queue_transfer_ds *qtds = ast_calloc(1, sizeof(*qtds));

	if (!qtds) {
		return NULL;
	}

	ast_channel_lock(qe->chan);
	if (!(ds = ast_datastore_alloc(&queue_transfer_info, NULL))) {
		ast_channel_unlock(qe->chan);
		ast_log(LOG_WARNING, "Unable to create transfer datastore. queue_log will not show attended transfer\n");
		return NULL;
	}

	qtds->qe = qe;
	/* This member is refcounted in try_calling, so no need to add it here, too */
	qtds->member = member;
	qtds->starttime = starttime;
	qtds->callcompletedinsl = callcompletedinsl;
	ds->data = qtds;
	ast_channel_datastore_add(qe->chan, ds);
	ast_channel_unlock(qe->chan);
	return ds;
}

struct queue_end_bridge {
	struct call_queue *q;
	struct ast_channel *chan;
};

static void end_bridge_callback_data_fixup(struct ast_bridge_config *bconfig, struct ast_channel *originator, struct ast_channel *terminator)
{
	struct queue_end_bridge *qeb = bconfig->end_bridge_callback_data;
	ao2_ref(qeb, +1);
	qeb->chan = originator;
}

static void end_bridge_callback(void *data)
{
	struct queue_end_bridge *qeb = data;
	struct call_queue *q = qeb->q;
	struct ast_channel *chan = qeb->chan;

	if (ao2_ref(qeb, -1) == 1) {
		set_queue_variables(q, chan);
		/* This unrefs the reference we made in try_calling when we allocated qeb */
		ao2_t_ref(q, -1, "Expire bridge_config reference");
	}
}

/*! \brief A large function which calls members, updates statistics, and bridges the caller and a member
 *
 * Here is the process of this function
 * 1. Process any options passed to the Queue() application. Options here mean the third argument to Queue()
 * 2. Iterate trough the members of the queue, creating a callattempt corresponding to each member. During this
 *    iteration, we also check the dialed_interfaces datastore to see if we have already attempted calling this
 *    member. If we have, we do not create a callattempt. This is in place to prevent call forwarding loops. Also
 *    during each iteration, we calculate a metric to determine which members should be rung when.
 * 3. Call ring_one to place a call to the appropriate member(s)
 * 4. Call wait_for_answer to wait for an answer. If no one answers, return.
 * 5. Take care of any holdtime announcements, member delays, or other options which occur after a call has been answered.
 * 6. Start the monitor or mixmonitor if the option is set
 * 7. Remove the caller from the queue to allow other callers to advance
 * 8. Bridge the call.
 * 9. Do any post processing after the call has disconnected.
 *
 * \param[in] qe the queue_ent structure which corresponds to the caller attempting to reach members
 * \param[in] options the options passed as the third parameter to the Queue() application
 * \param[in] announceoverride filename to play to user when waiting 
 * \param[in] url the url passed as the fourth parameter to the Queue() application
 * \param[in,out] tries the number of times we have tried calling queue members
 * \param[out] noption set if the call to Queue() has the 'n' option set.
 * \param[in] agi the agi passed as the fifth parameter to the Queue() application
 * \param[in] macro the macro passed as the sixth parameter to the Queue() application
 * \param[in] gosub the gosub passed as the seventh parameter to the Queue() application
 * \param[in] ringing 1 if the 'r' option is set, otherwise 0
 */
static int try_calling(struct queue_ent *qe, const char *options, char *announceoverride, const char *url, int *tries, int *noption, const char *agi, const char *macro, const char *gosub, int ringing)
{
	struct member *cur;
	struct callattempt *outgoing = NULL; /* the list of calls we are building */
	int to, orig;
	char oldexten[AST_MAX_EXTENSION]="";
	char oldcontext[AST_MAX_CONTEXT]="";
	char interfacevar[256]="";
	struct ast_channel *peer;
	struct ast_channel *which;
	struct callattempt *lpeer;
	struct member *member;
	struct ast_app *application;
	int res = 0, bridge = 0;
	int numbusies = 0;
	int x=0;
	const char *announce = NULL;
	char digit = 0;
	struct timeval callstart;
	struct timeval now;
	struct ast_bridge_config bridge_config;
	char nondataquality = 1;
	char *agiexec = NULL;
	char *macroexec = NULL;
	char *gosubexec = NULL;
	const char *monitorfilename;
	const char *monitor_exec;
	const char *monitor_options;
	char tmpid[256], tmpid2[256];
	char meid[1024], meid2[1024];
	char mixmonargs[1512];
	struct ast_app *mixmonapp = NULL;
	char *p;
	char vars[2048];
	int forwardsallowed = 1;
	int update_connectedline = 1;
	int callcompletedinsl;
	struct ao2_iterator memi;
	struct ast_datastore *datastore, *transfer_ds;
	struct queue_end_bridge *queue_end_bridge = NULL;
	struct ast_dialed_interface *di;
	struct ast_party_connected_line connected;
	struct ao2_iterator aiter;
	AST_LIST_HEAD(, ast_dialed_interface) *dialed_interfaces;

	memset(&bridge_config, 0, sizeof(bridge_config));
	tmpid[0] = 0;
	meid[0] = 0;
	now = ast_tvnow();

	/* If we've already exceeded our timeout, then just stop
	 * This should be extremely rare. queue_exec will take care
	 * of removing the caller and reporting the timeout as the reason.
	 */
	if (!ast_tvzero(qe->expire) && (ast_tvcmp(now, qe->expire) >= 0)) {
		res = 0;
		goto out;
	}

	for (; options && *options; options++)
		switch (*options) {
		case 't':
			ast_set_flag(&(bridge_config.features_callee), AST_FEATURE_REDIRECT);
			break;
		case 'T':
			ast_set_flag(&(bridge_config.features_caller), AST_FEATURE_REDIRECT);
			break;
		case 'w':
			ast_set_flag(&(bridge_config.features_callee), AST_FEATURE_AUTOMON);
			break;
		case 'W':
			ast_set_flag(&(bridge_config.features_caller), AST_FEATURE_AUTOMON);
			break;
		case 'c':
			ast_set_flag(&(bridge_config.features_caller), AST_FEATURE_NO_H_EXTEN);
			break;
		case 'd':
			nondataquality = 0;
			break;
		case 'h':
			ast_set_flag(&(bridge_config.features_callee), AST_FEATURE_DISCONNECT);
			break;
		case 'H':
			ast_set_flag(&(bridge_config.features_caller), AST_FEATURE_DISCONNECT);
			break;
		case 'k':
			ast_set_flag(&(bridge_config.features_callee), AST_FEATURE_PARKCALL);
			break;
		case 'K':
			ast_set_flag(&(bridge_config.features_caller), AST_FEATURE_PARKCALL);
			break;
		case 'n':
			if (qe->parent->strategy == QUEUE_STRATEGY_RRMEMORY ||
			    qe->parent->strategy == QUEUE_STRATEGY_LINEAR ||
			    qe->parent->strategy == QUEUE_STRATEGY_RRORDERED) {
				(*tries)++;
			} else {
				*tries = ao2_container_count(qe->parent->data->members);
			}
			*noption = 1;
			break;
		case 'i':
			forwardsallowed = 0;
			break;
		case 'I':
			update_connectedline = 0;
			break;
		case 'x':
			ast_set_flag(&(bridge_config.features_callee), AST_FEATURE_AUTOMIXMON);
			break;
		case 'X':
			ast_set_flag(&(bridge_config.features_caller), AST_FEATURE_AUTOMIXMON);
			break;
		case 'C':
			qe->cancel_answered_elsewhere = 1;
			break;
		}

	/* if the calling channel has the ANSWERED_ELSEWHERE flag set, make sure this is inherited. 
		(this is mainly to support chan_local)
	*/
	if (ast_test_flag(qe->chan, AST_FLAG_ANSWERED_ELSEWHERE)) {
		qe->cancel_answered_elsewhere = 1;
	}

	ast_party_connected_line_init(&connected);
	ast_channel_lock(qe->chan);
	/*
	 * Seed the callattempt's connected line information with previously
	 * acquired connected line info from the queued channel.  The
	 * previously acquired connected line info could have been set
	 * through the CONNECTED_LINE dialplan function.
	 */
	ast_party_connected_line_copy(&connected, &qe->chan->connected);
	datastore = ast_channel_datastore_find(qe->chan, &dialed_interface_info, NULL);
	ast_channel_unlock(qe->chan);

	if (!datastore &&
	    (datastore = ast_datastore_alloc(&dialed_interface_info, NULL))) {
		datastore->inheritance = DATASTORE_INHERIT_FOREVER;
		if (!(dialed_interfaces = ast_calloc(1, sizeof(*dialed_interfaces)))) {
			goto out;
		}
		datastore->data = dialed_interfaces;
		AST_LIST_HEAD_INIT(dialed_interfaces);

		ast_channel_lock(qe->chan);
		ast_channel_datastore_add(qe->chan, datastore);
		ast_channel_unlock(qe->chan);
	} else if (datastore) {
		dialed_interfaces = datastore->data;
	} else {
		goto out;
	}

	ast_debug(1, "%s is trying to call a queue member.\n", qe->chan->name);

	if (!ast_strlen_zero(announceoverride)) {
		announce = announceoverride;
	} else if (!ast_strlen_zero(qe->parent->announce)) {
		announce = qe->parent->announce;
	}

	memi = ao2_iterator_init(qe->parent->data->members, 0);
	while ((cur = ao2_iterator_next(&memi))) {
		AST_LIST_LOCK(dialed_interfaces);
		AST_LIST_TRAVERSE(dialed_interfaces, di, list) {
			if (!strcasecmp(cur->interface, di->interface)) {
				ast_debug(1, "Skipping dialing interface '%s' since it has already been dialed\n",
					di->interface);
				break;
			}
		}
		AST_LIST_UNLOCK(dialed_interfaces);

		if (di) {
			ao2_ref(cur, -1);
			continue;
		}

		/* It is always ok to dial a Local interface.  We only keep track of
		 * which "real" interfaces have been dialed.  The Local channel will
		 * inherit this list so that if it ends up dialing a real interface,
		 * it won't call one that has already been called. */
		if (strncasecmp(cur->interface, "Local/", 6)) {
			if (!(di = ast_calloc(1, sizeof(*di) + strlen(cur->interface)))) {
				ao2_ref(cur, -1);
				ao2_iterator_destroy(&memi);
				goto out;
			}
			strcpy(di->interface, cur->interface);

			AST_LIST_LOCK(dialed_interfaces);
			AST_LIST_INSERT_TAIL(dialed_interfaces, di, list);
			AST_LIST_UNLOCK(dialed_interfaces);
		}

		/* the ref for member is passed to this attempt*/
		if ((outgoing = new_attempt(qe, cur, x++))) {
			/* Put them in the list of outgoing thingies...  We're ready now.
			   XXX If we're forcibly removed, these outgoing calls won't get
			   hung up XXX */
			ast_party_connected_line_copy(&outgoing->connected, &connected);
			ao2_link(qe->attempts, outgoing);

			/* If this line is up, don't try anybody else */
			if (outgoing->chan && (outgoing->chan->_state == AST_STATE_UP)) {
				break;
			}
			ao2_ref(outgoing, -1);
		} else {
			ao2_ref(cur, -1);
		}
	}
	ao2_iterator_destroy(&memi);

	if (qe->parent->timeoutpriority == TIMEOUT_PRIORITY_APP) {
		/* Application arguments have higher timeout priority (behaviour for <=1.6) */
		if (!ast_tvzero(qe->expire) && (!qe->parent->timeout || (ast_tvdiff_sec(qe->expire, now) <= qe->parent->timeout))) {
			to = ast_tvdiff_sec(qe->expire, now) * 1000;
		} else {
			to = (qe->parent->timeout) ? qe->parent->timeout * 1000 : -1;
		}
	} else {
		/* Config timeout is higher priority thatn application timeout */
		if (!ast_tvzero(qe->expire) && (ast_tvcmp(now, qe->expire) >= 0)) {
			to = 0;
		} else if (qe->parent->timeout) {
			to = qe->parent->timeout * 1000;
		} else {
			to = -1;
		}
	}
	orig = to;
	++qe->pending;
	ring_one(qe, &numbusies);
	lpeer = wait_for_answer(qe, outgoing, &to, &digit, numbusies, ast_test_flag(&(bridge_config.features_caller), AST_FEATURE_DISCONNECT), forwardsallowed, update_connectedline);
	/* The ast_channel_datastore_remove() function could fail here if the
	 * datastore was moved to another channel during a masquerade. If this is
	 * the case, don't free the datastore here because later, when the channel
	 * to which the datastore was moved hangs up, it will attempt to free this
	 * datastore again, causing a crash
	 */
	ast_channel_lock(qe->chan);
	if (datastore && !ast_channel_datastore_remove(qe->chan, datastore)) {
		ast_datastore_free(datastore);
	}
	ast_channel_unlock(qe->chan);

	if (qe->parent->strategy == QUEUE_STRATEGY_RRMEMORY || qe->parent->strategy == QUEUE_STRATEGY_RRORDERED) {
		store_next_rr(qe);

	} else if (qe->parent->strategy == QUEUE_STRATEGY_LINEAR) {
		store_next_lin(qe);
	}

	peer = lpeer ? lpeer->chan : NULL;
	if (!peer) {
		qe->pending = 0;
		if (to) {
			/* Must gotten hung up */
			res = -1;
		} else {
			/* User exited by pressing a digit */
			res = digit;
		}
		if (res == -1)
			ast_debug(1, "%s: Nobody answered.\n", qe->chan->name);
		if (ast_cdr_isset_unanswered()) {
			/* channel contains the name of one of the outgoing channels
			   in its CDR; zero out this CDR to avoid a dual-posting */
			struct callattempt *o;
			aiter = ao2_iterator_init(qe->attempts, 0);
			while ((o = ao2_iterator_next(&aiter))) {
				if (!o->chan) {
					ao2_ref(o, -1);
					continue;
				}
				if (strcmp(o->chan->cdr->dstchannel, qe->chan->cdr->dstchannel) == 0) {
					ast_set_flag(o->chan->cdr, AST_CDR_FLAG_POST_DISABLED);
					ao2_ref(o, -1);
					break;
				}
				ao2_ref(o, -1);
			}
			ao2_iterator_destroy(&aiter);
		}
		if (lpeer) {
			ao2_ref(lpeer, -1);
		}
	} else { /* peer is valid */
		/* Ah ha!  Someone answered within the desired timeframe.  Of course after this
		   we will always return with -1 so that it is hung up properly after the
		   conversation.  */
		if (!strcmp(qe->chan->tech->type, "DAHDI")) {
			ast_channel_setoption(qe->chan, AST_OPTION_TONE_VERIFY, &nondataquality, sizeof(nondataquality), 0);
		}
		if (!strcmp(peer->tech->type, "DAHDI")) {
			ast_channel_setoption(peer, AST_OPTION_TONE_VERIFY, &nondataquality, sizeof(nondataquality), 0);
		}
		/* Update parameters for the queue */
		now = ast_tvnow();
		recalc_holdtime(qe, ast_tvdiff_sec(now, qe->start));
		callcompletedinsl = (ast_tvdiff_sec(now, qe->start) <= qe->parent->servicelevel);
		/* lpeer holds the ref for member and we hold a ref for lpeer */
		member = lpeer->member;
		hangupcalls(qe, lpeer);
		outgoing = NULL;
		if (announce || qe->parent->reportholdtime || qe->parent->memberdelay) {
			int res2;

			res2 = ast_autoservice_start(qe->chan);
			if (!res2) {
				if (qe->parent->memberdelay) {
					ast_log(LOG_NOTICE, "Delaying member connect for %d seconds\n", qe->parent->memberdelay);
					res2 |= ast_safe_sleep(peer, qe->parent->memberdelay * 1000);
				}
				if (!res2 && announce) {
					play_file(peer, announce);
				}
				if (!res2 && qe->parent->reportholdtime) {
					if (!play_file(peer, qe->parent->sound_reporthold)) {
						int holdtime, holdtimesecs;

						now = ast_tvnow();
						holdtime = abs(ast_tvdiff_sec(now, qe->start) / 60);
						holdtimesecs = abs(ast_tvdiff_sec(now, qe->start) % 60);
						if (holdtime > 0) {
							ast_say_number(peer, holdtime, AST_DIGIT_ANY, peer->language, NULL);
							play_file(peer, qe->parent->sound_minutes);
						}
						if (holdtimesecs > 1) {
							ast_say_number(peer, holdtimesecs, AST_DIGIT_ANY, peer->language, NULL);
							play_file(peer, qe->parent->sound_seconds);
						}
					}
				}
			}
			res2 |= ast_autoservice_stop(qe->chan);
			if (ast_check_hangup(peer)) {
				/* Agent must have hung up */
				ao2_lock(member);
				ast_log(LOG_WARNING, "Agent on %s hungup on the customer.\n", peer->name);
				ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "AGENTDUMP", "%s", "");
				if (qe->parent->eventwhencalled)
					manager_event(EVENT_FLAG_AGENT, "AgentDump",
							"Queue: %s\r\n"
							"Uniqueid: %s\r\n"
							"Channel: %s\r\n"
							"Member: %s\r\n"
							"MemberName: %s\r\n"
							"%s",
							qe->parent->name, qe->chan->uniqueid, peer->name, member->interface, member->membername,
							qe->parent->eventwhencalled == QUEUE_EVENT_VARIABLES ? vars2manager(qe->chan, vars, sizeof(vars)) : "");
				ao2_unlock(member);
				ao2_ref(lpeer, -1);
				ast_hangup(peer);
				goto out;
			} else if (res2) {
				/* Caller must have hung up just before being connected*/
				ast_log(LOG_NOTICE, "Caller was about to talk to agent on %s but the caller hungup.\n", peer->name);
				ao2_lock(member);
				ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "ABANDON", "%d|%d|%ld", qe->pos, qe->opos, (long)ast_tvdiff_sec(ast_tvnow(), qe->start));
				ao2_unlock(member);
				record_abandoned(qe);
				ao2_unlink(qe->attempts, lpeer);
				ao2_ref(lpeer, -1);
				ast_hangup(peer);
				return -1;
			}
		}
		/* Stop music on hold */
		if (ringing)
			ast_indicate(qe->chan,-1);
		else
			ast_moh_stop(qe->chan);
		/* If appropriate, log that we have a destination channel */
		if (qe->chan->cdr) {
			ast_cdr_setdestchan(qe->chan->cdr, peer->name);
		}
		/* Make sure channels are compatible */
		res = ast_channel_make_compatible(qe->chan, peer);
		if (res < 0) {
			ao2_lock(member);
			ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "SYSCOMPAT", "%s", "");
			ao2_unlock(member);
			ast_log(LOG_WARNING, "Had to drop call because I couldn't make %s compatible with %s\n", qe->chan->name, peer->name);
			record_abandoned(qe);
			ast_cdr_failed(qe->chan->cdr);
			ao2_unlink(qe->attempts, lpeer);
			ao2_ref(lpeer, -1);
			ast_hangup(peer);
			return -1;
		}

		/* Play announcement to the caller telling it's his turn if defined */
		if (!ast_strlen_zero(qe->parent->sound_callerannounce)) {
			if (play_file(qe->chan, qe->parent->sound_callerannounce))
				ast_log(LOG_WARNING, "Announcement file '%s' is unavailable, continuing anyway...\n", qe->parent->sound_callerannounce);
		}

		/* if setinterfacevar is defined, make member variables available to the channel */
		/* use  pbx_builtin_setvar to set a load of variables with one call */
		if (qe->parent->setinterfacevar) {
			ao2_lock(member);
			snprintf(interfacevar, sizeof(interfacevar), "MEMBERINTERFACE=%s,MEMBERNAME=%s,MEMBERCALLS=%d,MEMBERLASTCALL=%ld,MEMBERPENALTY=%d,MEMBERDYNAMIC=%d,MEMBERREALTIME=%d",
				member->interface, member->membername, member->calls, (long)member->lastcall.tv_sec, member->penalty, member->dynamic, member->realtime);
			pbx_builtin_setvar_multiple(qe->chan, interfacevar);
			pbx_builtin_setvar_multiple(peer, interfacevar);
			ao2_unlock(member);
		}

		/* if setqueueentryvar is defined, make queue entry (i.e. the caller) variables available to the channel */
		/* use  pbx_builtin_setvar to set a load of variables with one call */
		if (qe->parent->setqueueentryvar) {
			snprintf(interfacevar, sizeof(interfacevar), "QEHOLDTIME=%ld,QEORIGINALPOS=%d",
				(long)ast_tvdiff_sec(ast_tvnow(), qe->start), qe->opos);
			pbx_builtin_setvar_multiple(qe->chan, interfacevar);
			pbx_builtin_setvar_multiple(peer, interfacevar);
		}

		/* try to set queue variables if configured to do so*/
		set_queue_variables(qe->parent, qe->chan);
		set_queue_variables(qe->parent, peer);

		ast_channel_lock(qe->chan);
		if ((monitorfilename = pbx_builtin_getvar_helper(qe->chan, "MONITOR_FILENAME"))) {
				monitorfilename = ast_strdupa(monitorfilename);
		}
		ast_channel_unlock(qe->chan);
		/* Begin Monitoring */
		if (!ast_strlen_zero(qe->parent->monfmt)) {
			if (!qe->parent->montype) {
				const char *monexec, *monargs;
				ast_debug(1, "Starting Monitor as requested.\n");
				ast_channel_lock(qe->chan);
				if ((monexec = pbx_builtin_getvar_helper(qe->chan, "MONITOR_EXEC")) || (monargs = pbx_builtin_getvar_helper(qe->chan, "MONITOR_EXEC_ARGS"))) {
					which = qe->chan;
					monexec = monexec ? ast_strdupa(monexec) : NULL;
				}
				else
					which = peer;
				ast_channel_unlock(qe->chan);
				if (monitorfilename) {
					ast_monitor_start(which, qe->parent->monfmt, monitorfilename, 1, X_REC_IN | X_REC_OUT);
				} else if (qe->chan->cdr) {
					ast_monitor_start(which, qe->parent->monfmt, qe->chan->cdr->uniqueid, 1, X_REC_IN | X_REC_OUT);
				} else {
					/* Last ditch effort -- no CDR, make up something */
					snprintf(tmpid, sizeof(tmpid), "chan-%lx", ast_random());
					ast_monitor_start(which, qe->parent->monfmt, tmpid, 1, X_REC_IN | X_REC_OUT);
				}
				if (!ast_strlen_zero(monexec)) {
					ast_monitor_setjoinfiles(which, 1);
				}
			} else {
				mixmonapp = pbx_findapp("MixMonitor");
				
				if (mixmonapp) {
					ast_debug(1, "Starting MixMonitor as requested.\n");
					if (!monitorfilename) {
						if (qe->chan->cdr) {
							ast_copy_string(tmpid, qe->chan->cdr->uniqueid, sizeof(tmpid));
						} else {
							snprintf(tmpid, sizeof(tmpid), "chan-%lx", ast_random());
						}
					} else {
						const char *m = monitorfilename;
						for (p = tmpid2; p < tmpid2 + sizeof(tmpid2) - 1; p++, m++) {
							switch (*m) {
							case '^':
								if (*(m + 1) == '{')
									*p = '$';
								break;
							case ',':
								*p++ = '\\';
								/* Fall through */
							default:
								*p = *m;
							}
							if (*m == '\0')
								break;
						}
						if (p == tmpid2 + sizeof(tmpid2))
							tmpid2[sizeof(tmpid2) - 1] = '\0';

						pbx_substitute_variables_helper(qe->chan, tmpid2, tmpid, sizeof(tmpid) - 1);
					}

					ast_channel_lock(qe->chan);
					if ((monitor_exec = pbx_builtin_getvar_helper(qe->chan, "MONITOR_EXEC"))) {
							monitor_exec = ast_strdupa(monitor_exec);
					}
					if ((monitor_options = pbx_builtin_getvar_helper(qe->chan, "MONITOR_OPTIONS"))) {
							monitor_options = ast_strdupa(monitor_options);
					} else {
						monitor_options = "";
					}
					ast_channel_unlock(qe->chan);

					if (monitor_exec) {
						const char *m = monitor_exec;
						for (p = meid2; p < meid2 + sizeof(meid2) - 1; p++, m++) {
							switch (*m) {
							case '^':
								if (*(m + 1) == '{')
									*p = '$';
								break;
							case ',':
								*p++ = '\\';
								/* Fall through */
							default:
								*p = *m;
							}
							if (*m == '\0')
								break;
						}
						if (p == meid2 + sizeof(meid2))
							meid2[sizeof(meid2) - 1] = '\0';

						pbx_substitute_variables_helper(qe->chan, meid2, meid, sizeof(meid) - 1);
					}

					snprintf(tmpid2, sizeof(tmpid2), "%s.%s", tmpid, qe->parent->monfmt);

					if (!ast_strlen_zero(monitor_exec)) {
						snprintf(mixmonargs, sizeof(mixmonargs), "%s,b%s,%s", tmpid2, monitor_options, monitor_exec);
					} else {
						snprintf(mixmonargs, sizeof(mixmonargs), "%s,b%s", tmpid2, monitor_options);
					}
					ast_debug(1, "Arguments being passed to MixMonitor: %s\n", mixmonargs);
					/* We purposely lock the CDR so that pbx_exec does not update the application data */
					if (qe->chan->cdr) {
						ast_set_flag(qe->chan->cdr, AST_CDR_FLAG_LOCKED);
					}
					pbx_exec(qe->chan, mixmonapp, mixmonargs);
					if (qe->chan->cdr) {
						ast_clear_flag(qe->chan->cdr, AST_CDR_FLAG_LOCKED);
					}
				} else {
					ast_log(LOG_WARNING, "Asked to run MixMonitor on this call, but cannot find the MixMonitor app!\n");
				}
			}
		}
		/* Drop out of the queue at this point, to prepare for next caller */
		leave_queue(qe);			
		if (!ast_strlen_zero(url) && ast_channel_supports_html(peer)) {
			ast_debug(1, "app_queue: sendurl=%s.\n", url);
			ast_channel_sendurl(peer, url);
		}
		
		/* run a macro for this connection if defined. The macro simply returns, no action is taken on the result */
		/* use macro from dialplan if passed as a option, otherwise use the default queue macro */
		if (!ast_strlen_zero(macro)) {
				macroexec = ast_strdupa(macro);
		} else {
			if (qe->parent->membermacro) {
				macroexec = ast_strdupa(qe->parent->membermacro);
			}
		}

		if (!ast_strlen_zero(macroexec)) {
			ast_debug(1, "app_queue: macro=%s.\n", macroexec);

			res = ast_autoservice_start(qe->chan);
			if (res) {
				ast_log(LOG_ERROR, "Unable to start autoservice on calling channel\n");
				res = -1;
			}
			
			application = pbx_findapp("Macro");

			if (application) {
				res = pbx_exec(peer, application, macroexec);
				ast_debug(1, "Macro exited with status %d\n", res);
				res = 0;
			} else {
				ast_log(LOG_ERROR, "Could not find application Macro\n");
				res = -1;
			}

			if (ast_autoservice_stop(qe->chan) < 0) {
				ast_log(LOG_ERROR, "Could not stop autoservice on calling channel\n");
				res = -1;
			}
		}

		/* run a gosub for this connection if defined. The gosub simply returns, no action is taken on the result */
		/* use gosub from dialplan if passed as a option, otherwise use the default queue gosub */
		if (!ast_strlen_zero(gosub)) {
				gosubexec = ast_strdupa(gosub);
		} else {
			if (qe->parent->membergosub) {
				gosubexec = ast_strdupa(qe->parent->membergosub);
			}
		}

		if (!ast_strlen_zero(gosubexec)) {
			ast_debug(1, "app_queue: gosub=%s.\n", gosubexec);

			res = ast_autoservice_start(qe->chan);
			if (res) {
				ast_log(LOG_ERROR, "Unable to start autoservice on calling channel\n");
				res = -1;
			}

			application = pbx_findapp("Gosub");

			if (application) {
				char *gosub_args, *gosub_argstart;

				/* Set where we came from */
				ast_copy_string(peer->context, "app_queue_gosub_virtual_context", sizeof(peer->context));
				ast_copy_string(peer->exten, "s", sizeof(peer->exten));
				peer->priority = 0;

				gosub_argstart = strchr(gosubexec, ',');
				if (gosub_argstart) {
					const char *what_is_s = "s";
					*gosub_argstart = 0;
					if (!ast_exists_extension(peer, gosubexec, "s", 1, S_COR(peer->caller.id.number.valid, peer->caller.id.number.str, NULL)) &&
						 ast_exists_extension(peer, gosubexec, "~~s~~", 1, S_COR(peer->caller.id.number.valid, peer->caller.id.number.str, NULL))) {
						what_is_s = "~~s~~";
					}
					if (asprintf(&gosub_args, "%s,%s,1(%s)", gosubexec, what_is_s, gosub_argstart + 1) < 0) {
						ast_log(LOG_WARNING, "asprintf() failed: %s\n", strerror(errno));
						gosub_args = NULL;
					}
					*gosub_argstart = ',';
				} else {
					const char *what_is_s = "s";
					if (!ast_exists_extension(peer, gosubexec, "s", 1, S_COR(peer->caller.id.number.valid, peer->caller.id.number.str, NULL)) &&
						 ast_exists_extension(peer, gosubexec, "~~s~~", 1, S_COR(peer->caller.id.number.valid, peer->caller.id.number.str, NULL))) {
						what_is_s = "~~s~~";
					}
					if (asprintf(&gosub_args, "%s,%s,1", gosubexec, what_is_s) < 0) {
						ast_log(LOG_WARNING, "asprintf() failed: %s\n", strerror(errno));
						gosub_args = NULL;
					}
				}
				if (gosub_args) {
					res = pbx_exec(peer, application, gosub_args);
					if (!res) {
						struct ast_pbx_args args;
						memset(&args, 0, sizeof(args));
						args.no_hangup_chan = 1;
						ast_pbx_run_args(peer, &args);
					}
					ast_free(gosub_args);
					ast_debug(1, "Gosub exited with status %d\n", res);
				} else {
					ast_log(LOG_ERROR, "Could not Allocate string for Gosub arguments -- Gosub Call Aborted!\n");
				}
			} else {
				ast_log(LOG_ERROR, "Could not find application Gosub\n");
				res = -1;
			}
		
			if (ast_autoservice_stop(qe->chan) < 0) {
				ast_log(LOG_ERROR, "Could not stop autoservice on calling channel\n");
				res = -1;
			}
		}

		if (!ast_strlen_zero(agi)) {
			ast_debug(1, "app_queue: agi=%s.\n", agi);
			application = pbx_findapp("agi");
			if (application) {
				agiexec = ast_strdupa(agi);
				pbx_exec(qe->chan, application, agiexec);
			} else
				ast_log(LOG_WARNING, "Asked to execute an AGI on this channel, but could not find application (agi)!\n");
		}
		qe->handled++;
		callstart = ast_tvnow();

		ao2_lock(member);
		if (qe->parent->eventwhencalled) {
			manager_event(EVENT_FLAG_AGENT, "AgentConnect",
					"Queue: %s\r\n"
					"Uniqueid: %s\r\n"
					"Channel: %s\r\n"
					"Member: %s\r\n"
					"MemberName: %s\r\n"
					"Holdtime: %ld\r\n"
					"BridgedChannel: %s\r\n"
					"Ringtime: %ld\r\n"
					"%s",
					qe->parent->name, qe->chan->uniqueid, peer->name, member->interface, member->membername,
					(long)ast_tvdiff_sec(callstart, qe->start), peer->uniqueid, (long)(orig - to > 0 ? (orig - to) / 1000 : 0),
					qe->parent->eventwhencalled == QUEUE_EVENT_VARIABLES ? vars2manager(qe->chan, vars, sizeof(vars)) : "");
		}

		ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "CONNECT", "%ld|%s|%ld",
					(long)ast_tvdiff_sec(ast_tvnow(), qe->start), peer->uniqueid,
					(long)(orig - to > 0 ? (orig - to) / 1000 : 0));
		ao2_unlock(member);

		if (qe->chan->cdr) {
			struct ast_cdr *cdr;
			struct ast_cdr *newcdr;

			/* Only work with the last CDR in the stack*/
			cdr = qe->chan->cdr;
			while (cdr->next) {
				cdr = cdr->next;
			}

			/* If this CDR is not related to us add new one*/
			if ((strcasecmp(cdr->uniqueid, qe->chan->uniqueid)) &&
			    (strcasecmp(cdr->linkedid, qe->chan->uniqueid)) &&
			    (newcdr = ast_cdr_dup(cdr))) {
				ast_channel_lock(qe->chan);
				ast_cdr_init(newcdr, qe->chan);
				ast_cdr_reset(newcdr, 0);
				cdr = ast_cdr_append(cdr, newcdr);
				cdr = cdr->next;
				ast_channel_unlock(qe->chan);
			}

			if (update_cdr) {
				ao2_lock(member);
				ast_copy_string(cdr->dstchannel, member->membername, sizeof(cdr->dstchannel));
				ao2_unlock(member);
			}
		}

		ast_copy_string(oldcontext, qe->chan->context, sizeof(oldcontext));
		ast_copy_string(oldexten, qe->chan->exten, sizeof(oldexten));

		if ((queue_end_bridge = ao2_alloc(sizeof(*queue_end_bridge), NULL))) {
			queue_end_bridge->q = qe->parent;
			queue_end_bridge->chan = qe->chan;
			bridge_config.end_bridge_callback = end_bridge_callback;
			bridge_config.end_bridge_callback_data = queue_end_bridge;
			bridge_config.end_bridge_callback_data_fixup = end_bridge_callback_data_fixup;
			/* Since queue_end_bridge can survive beyond the life of this call to Queue, we need
			 * to make sure to increase the refcount of this queue so it cannot be freed until we
			 * are done with it. We remove this reference in end_bridge_callback.
			 */
			ao2_t_ref(qe->parent, 1, "For bridge_config reference");
		}

		/* The call was picked up elsewhere log the original interface the channel picking up the call hold time and position */
		ast_channel_lock_both(peer, qe->chan);
		if (ast_channel_datastore_find(peer, &pickup_target_info, NULL)) {
			ao2_unlink(qe->attempts, lpeer);
			ao2_ref(member, 1);
			ao2_lock(member);
			ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "PICKUP", "%s|%s|%ld|%d",
						member->interface, peer->name, (long)ast_tvdiff_sec(callstart, qe->start), qe->opos);
			ao2_unlock(member);
			ao2_ref(lpeer, -1);
			lpeer = NULL;
			ast_channel_unlock(peer);
			ast_channel_unlock(qe->chan);
		} else {
			ast_channel_unlock(peer);
			ast_channel_unlock(qe->chan);
			ao2_lock(member);
			ao2_lock(member->device);
			member->device->active++;
			lpeer->active = 1;
			if (lpeer->reserved) {
				lpeer->reserved = 0;
				member->device->reserved--;
			}
			ao2_unlock(member->device);
			ao2_unlock(member);
		}

		transfer_ds = setup_transfer_datastore(qe, member, callstart, callcompletedinsl);
		bridge = ast_bridge_call(qe->chan,peer, &bridge_config);

		/* If the queue member did an attended transfer, then the TRANSFER already was logged in the queue_log
		 * when the masquerade occurred. These other "ending" queue_log messages are unnecessary, except for
		 * the AgentComplete manager event
		 */
		ast_channel_lock(qe->chan);
		if (!attended_transfer_occurred(qe->chan)) {
			struct ast_datastore *tds;

			/* detect a blind transfer */
			ao2_lock(member);
			if (!(qe->chan->_softhangup | peer->_softhangup) && (strcasecmp(oldcontext, qe->chan->context) || strcasecmp(oldexten, qe->chan->exten))) {
				ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "TRANSFER", "%s|%s|%ld|%ld|%d",
					qe->chan->exten, qe->chan->context, (long)ast_tvdiff_sec(callstart, qe->start),
					(long)ast_tvdiff_sec(ast_tvnow(), callstart), qe->opos);
				send_agent_complete(qe, qe->parent->name, peer, member, callstart, vars, sizeof(vars), TRANSFER);
			} else if (ast_check_hangup(qe->chan)) {
				ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "COMPLETECALLER", "%ld|%ld|%d",
					(long)ast_tvdiff_sec(callstart, qe->start), (long)ast_tvdiff_sec(ast_tvnow(), callstart), qe->opos);
				send_agent_complete(qe, qe->parent->name, peer, member, callstart, vars, sizeof(vars), CALLER);
			} else {
				ast_queue_log(qe->parent->name, qe->chan->uniqueid, member->membername, "COMPLETEAGENT", "%ld|%ld|%d",
					(long)ast_tvdiff_sec(callstart, qe->start), (long)ast_tvdiff_sec(ast_tvnow(), callstart), qe->opos);
				send_agent_complete(qe, qe->parent->name, peer, member, callstart, vars, sizeof(vars), AGENT);
			}
			ao2_unlock(member);
			if ((tds = ast_channel_datastore_find(qe->chan, &queue_transfer_info, NULL))) {
				ast_channel_datastore_remove(qe->chan, tds);
			}
			ast_channel_unlock(qe->chan);
			update_queue(qe->parent, member, callcompletedinsl, ast_tvdiff_sec(ast_tvnow(), callstart));
		} else {
			ast_channel_unlock(qe->chan);

			/* We already logged the TRANSFER on the queue_log, but we still need to send the AgentComplete event */
			ao2_lock(member);
			send_agent_complete(qe, qe->parent->name, peer, member, callstart, vars, sizeof(vars), TRANSFER);
			ao2_unlock(member);
		}

		if (transfer_ds) {
			ast_datastore_free(transfer_ds);
		}
		if (lpeer) {
			ao2_unlink(qe->attempts, lpeer);
			ao2_ref(lpeer, -1);
		} else {
			ao2_ref(member, -1);
		}
		ast_hangup(peer);
		res = bridge ? bridge : 1;
	}
out:
	hangupcalls(qe, NULL);

	return res;
}

static int wait_a_bit(struct queue_ent *qe)
{
	int retrywait = qe->parent->retry * 1000;

	int res = ast_waitfordigit(qe->chan, retrywait);
	if (res > 0 && !valid_exit(qe, res))
		res = 0;

	return res;
}

static struct member *interface_exists(struct call_queue *q, const char *interface)
{
	struct member *mem = NULL;
	struct ast_config *mcfg;
	const char *newm = NULL;

	if (q && !(mem = ao2_find(q->data->members, (char *)interface, 0))) {
		/* if no member is found in core lets load this member from realtime */
		if (!(mcfg = ast_load_realtime_multientry("queue_members", "interface", interface, "queue_name", q->name, SENTINEL))) {
			ast_log(AST_LOG_WARNING, "Failed to find member %s for queue %s\n", interface, q->name);
			return NULL;
		}
		while ((newm = ast_category_browse(mcfg, newm))) {
			handle_member_record(q, newm, mcfg, QUEUE_ADD_MEMBER_REALTIME, "REALTIME");
			mem = ao2_find(q->data->members, (char *)interface, 0);
		}
		ast_config_destroy(mcfg);
	}
	return mem;
}

/*! \brief Dump all members in a specific queue to the database
 *
 * <pm_family>/<queuename> = <interface>;<penalty>;<paused>;<state_interface>;<callinuse>[|...]
 */
static void dump_queue_members(struct call_queue *pm_queue)
{
	struct member *cur_member;
	char value[PM_MAX_LEN];
	int value_len = 0;
	int res;
	struct ao2_iterator mem_iter;

	memset(value, 0, sizeof(value));

	if (!pm_queue)
		return;

	mem_iter = ao2_iterator_init(pm_queue->data->members, 0);
	while ((cur_member = ao2_iterator_next(&mem_iter))) {
		ao2_lock(cur_member);
		if (!cur_member->dynamic || cur_member->dead) {
			ao2_unlock(cur_member);
			ao2_ref(cur_member, -1);
			continue;
		}

		res = snprintf(value + value_len, sizeof(value) - value_len, "%s%s;%d;%d;%s;%s;%d",
			value_len ? "|" : "", cur_member->interface, cur_member->penalty,cur_member->paused,
					cur_member->membername, cur_member->device->state_interface, cur_member->callinuse);
		ao2_unlock(cur_member);
		ao2_ref(cur_member, -1);

		if (res != strlen(value + value_len)) {
			ast_log(LOG_WARNING, "Could not create persistent member string, out of space\n");
			break;
		}
		value_len += res;
	}
	ao2_iterator_destroy(&mem_iter);

	if (value_len) {
		if (ast_db_put(pm_family, pm_queue->name, value)) {
			ast_log(LOG_WARNING, "failed to create persistent dynamic entry!\n");
		}
	} else {
		/* Delete the entry if the queue is empty or there is an error */
		ast_db_del(pm_family, pm_queue->name);
	}
}

/*! \brief Remove member from queue
 * \retval RES_NOT_DYNAMIC when they aren't a RT member
 * \retval RES_NOSUCHQUEUE queue does not exist
 * \retval RES_OKAY removed member from queue
 * \retval RES_EXISTS queue exists but no members
*/
static int remove_from_queue(const char *queuename, const char *interface, const char *source)
{
	struct call_queue *q;
	struct member *mem;
	int reload = 0;

	if (!(q = load_realtime_queue(queuename, NULL))) {
		return RES_NOSUCHQUEUE;
	}
	if (!(mem = interface_exists(q, interface))) {
		ao2_ref(q, -1);
		return RES_EXISTS;
	}
	ao2_lock(mem);
	/* XXX future changes should beware of this assumption!! */
	/*Change Penalty on realtime users*/
	if (mem->realtime && negative_penalty_invalid) {
		update_realtime_member_field(mem, q->name, "penalty", "-1");
	} else if (!mem->dynamic) {
		ao2_unlock(mem);
		ao2_ref(mem, -1);
		ao2_ref(q, -1);
		return RES_NOT_DYNAMIC;
	} else if (mem->dynamic) {
		reload = 1;
	}
	manager_event(EVENT_FLAG_AGENT, "QueueMemberRemoved",
		"Queue: %s\r\n"
		"Location: %s\r\n"
		"MemberName: %s\r\n",
		q->name, mem->interface, mem->membername);

	if (log_membername_as_agent) {
		ast_queue_log(q->name, source, mem->membername, "REMOVEMEMBER", "%s", "");
	} else {
		ast_queue_log(q->name, source, mem->interface, "REMOVEMEMBER", "%s", "");
	}

	ao2_unlock(mem);
	ao2_unlink(q->data->members, mem);
	ao2_ref(mem, -1);
	if (reload && queue_persistent_members) {
		dump_queue_members(q);
	}
	ao2_ref(q, -1);
	return RES_OKAY;
}

static int do_set_member_penalty_paused(struct call_queue *q, struct member *mem, int pause, int value, const char *reason)
{
	if (pause) {
		mem->paused = (value) ? 1 : 0;
		if (mem->realtime &&
		    update_realtime_member_field(mem, q->name, "paused", (value) ? "1" : "0")) {
			ast_log(LOG_WARNING, "Failed %spausing realtime member %s queue %s\n",
					(value) ? "" : "un", mem->membername, q->name);
			return -1;
		}

		ast_queue_log(q->name, "NONE", mem->membername, (value) ? "PAUSE" : "UNPAUSE", "%s", S_OR(reason, ""));

		if (!ast_strlen_zero(reason)) {
			manager_event(EVENT_FLAG_AGENT, "QueueMemberPaused",
				"Queue: %s\r\n"
				"Location: %s\r\n"
				"MemberName: %s\r\n"
				"Paused: %d\r\n"
				"Reason: %s\r\n",
					q->name, mem->interface, mem->membername, (value) ? 1 : 0, reason);
		} else {
			manager_event(EVENT_FLAG_AGENT, "QueueMemberPaused",
				"Queue: %s\r\n"
				"Location: %s\r\n"
				"MemberName: %s\r\n"
				"Paused: %d\r\n",
					q->name, mem->interface, mem->membername, (value) ? 1 : 0);
		}
	} else {
		mem->penalty = value;
		if (mem->realtime) {
			char *rtpenalty;
			if (!asprintf(&rtpenalty,"%i", mem->penalty) ||
			    update_realtime_member_field(mem, q->name, "penalty", rtpenalty)) {
				ast_log(LOG_WARNING, "Failed setting penalty %d on member %s queue %s\n", mem->penalty,
					mem->membername, q->name);
				return -1;
			}
		}

		ast_queue_log(q->name, "NONE", mem->interface, "PENALTY", "%d", mem->penalty);
		manager_event(EVENT_FLAG_AGENT, "QueueMemberPenalty",
					"Queue: %s\r\n"
					"Location: %s\r\n"
					"Penalty: %d\r\n",
			q->name, mem->interface, mem->penalty);
	}

	if (mem->dynamic && queue_persistent_members) {
		dump_queue_members(q);
	}

	return 0;
}


static int set_member_paused(const char *queuename, const char *interface, const char *reason, int paused)
{
	int found = 0;
	struct call_queue *q;
	struct member *mem;
	struct ao2_iterator queue_iter;

	if (!ast_strlen_zero(queuename)) {
		if (!(q = load_realtime_queue(queuename, NULL))) {
			return RESULT_FAILURE;
		}
		if (!(mem = interface_exists(q, interface))) {
			ao2_ref(q, -1);
			return RESULT_FAILURE;
		}
		ao2_lock(mem);
		found = !do_set_member_penalty_paused(q, mem, 1, paused, reason);
		ao2_unlock(mem);
		ao2_ref(mem, -1);
		ao2_ref(q, -1);
		return (!found) ? RESULT_FAILURE : RESULT_SUCCESS;
	}

	load_all_realtime_queues(NULL);

	/* Special event for when all queues are paused - individual events still generated */
	/* XXX In all other cases, we use the membername, but since this affects all queues, we cannot */
	ast_queue_log("NONE", "NONE", interface, (paused ? "PAUSEALL" : "UNPAUSEALL"), "%s", "");

	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate over queues"))) {
		if ((mem = interface_exists(q, interface))) {
			ao2_lock(mem);
			if (!do_set_member_penalty_paused(q, mem, 1, paused, reason)) {
				found ++;
			}
			ao2_unlock(mem);
			ao2_ref(mem, -1);
		}
		ao2_t_ref(q, -1, "Done with iterator");
	}
	ao2_iterator_destroy(&queue_iter);

	return found ? RESULT_SUCCESS : RESULT_FAILURE;
}

/* \brief Sets members penalty, if queuename=NULL we set member penalty in all the queues. */
static int set_member_penalty(const char *queuename, const char *interface, int penalty)
{
	int foundinterface = 0;
	struct call_queue *q;
	struct member *mem;
	struct ao2_iterator queue_iter;

	if (penalty < 0 && !negative_penalty_invalid) {
		ast_log(LOG_ERROR, "Invalid penalty (%d)\n", penalty);
		return RESULT_FAILURE;
	}

	if (!ast_strlen_zero(queuename)) {
		if (!(q = load_realtime_queue(queuename, NULL))) {
			return RESULT_FAILURE;
		}
		if (!(mem = interface_exists(q, interface))) {
			ao2_ref(q, -1);
			return RESULT_FAILURE;
		}

		ao2_lock(mem);
		do_set_member_penalty_paused(q, mem, 0, penalty, NULL);
		ao2_unlock(mem);
		ao2_ref(mem, -1);
		ao2_ref(q, -1);
		return RESULT_SUCCESS;
	}

	load_all_realtime_queues(NULL);

	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate over queues"))) {
		if ((mem = interface_exists(q, interface))) {
			ao2_lock(mem);
			if (!do_set_member_penalty_paused(q, mem, 0, penalty, NULL)) {
				foundinterface++;
			}
			ao2_unlock(mem);
			ao2_ref(mem, -1);
		}
		ao2_ref(q, -1);
	}

	if (foundinterface) {
		return RESULT_SUCCESS;
	} else {
		ast_log (LOG_ERROR, "Invalid interface\n");
	}

	return RESULT_FAILURE;
}

static void add_var_to_cat(struct ast_category *cat, const char *varname, const char *value)
{
	const char *file = (char *)cat;
	if (!ast_strlen_zero(value)) {
		ast_variable_append(cat, ast_variable_new(varname, value, file));
	}
}

static void pm_load_member_config(struct call_queue *q) {
	char *member;
	char *interface = NULL;
	char queue_data[PM_MAX_LEN];
	char *cur_ptr;
	struct ast_config *mcfg;
	struct ast_category *mcat;

	if (ast_db_get(pm_family, q->name, queue_data, PM_MAX_LEN)) {
		return;
	}

	if (!(mcfg = ast_config_new())) {
		return;
	}

	cur_ptr = queue_data;
	while ((member = strsep(&cur_ptr, ",|"))) {
		if (ast_strlen_zero(member)) {
			continue;
		}

		if (!(mcat = ast_category_new(strsep(&member, ";"), pm_family, -1))) {
			continue;
		}
		ast_category_append(mcfg, mcat);

		add_var_to_cat(mcat, "penalty", strsep(&member, ";"));
		add_var_to_cat(mcat, "paused", strsep(&member, ";"));
		add_var_to_cat(mcat, "membername", strsep(&member, ";"));
		add_var_to_cat(mcat, "state_interface", strsep(&member, ";"));
		add_var_to_cat(mcat, "callinuse", strsep(&member, ";"));
	}

	while ((interface = ast_category_browse(mcfg, interface))) {
		handle_member_record(q, interface, mcfg, QUEUE_ADD_MEMBER_DYNAMIC, "ASTDB");
	}
	ast_config_destroy(mcfg);
}

/*! \brief PauseQueueMember application */
static int pqm_exec(struct ast_channel *chan, const char *data)
{
	char *parse;
	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(interface);
		AST_APP_ARG(options);
		AST_APP_ARG(reason);
	);

	if (ast_strlen_zero(data)) {
		ast_log(LOG_WARNING, "PauseQueueMember requires an argument ([queuename],interface[,options][,reason])\n");
		return -1;
	}

	parse = ast_strdupa(data);

	AST_STANDARD_APP_ARGS(args, parse);

	if (ast_strlen_zero(args.interface)) {
		ast_log(LOG_WARNING, "Missing interface argument to PauseQueueMember ([queuename],interface[,options[,reason]])\n");
		return -1;
	}

	if (set_member_paused(args.queuename, args.interface, args.reason, 1)) {
		ast_log(LOG_WARNING, "Attempt to pause interface %s, not found\n", args.interface);
		pbx_builtin_setvar_helper(chan, "PQMSTATUS", "NOTFOUND");
		return 0;
	}

	pbx_builtin_setvar_helper(chan, "PQMSTATUS", "PAUSED");

	return 0;
}

/*! \brief UnPauseQueueMember application */
static int upqm_exec(struct ast_channel *chan, const char *data)
{
	char *parse;
	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(interface);
		AST_APP_ARG(options);
		AST_APP_ARG(reason);
	);

	if (ast_strlen_zero(data)) {
		ast_log(LOG_WARNING, "UnpauseQueueMember requires an argument ([queuename],interface[,options[,reason]])\n");
		return -1;
	}

	parse = ast_strdupa(data);

	AST_STANDARD_APP_ARGS(args, parse);

	if (ast_strlen_zero(args.interface)) {
		ast_log(LOG_WARNING, "Missing interface argument to PauseQueueMember ([queuename],interface[,options[,reason]])\n");
		return -1;
	}

	if (set_member_paused(args.queuename, args.interface, args.reason, 0)) {
		ast_log(LOG_WARNING, "Attempt to unpause interface %s, not found\n", args.interface);
		pbx_builtin_setvar_helper(chan, "UPQMSTATUS", "NOTFOUND");
		return 0;
	}

	pbx_builtin_setvar_helper(chan, "UPQMSTATUS", "UNPAUSED");

	return 0;
}

/*! \brief RemoveQueueMember application */
static int rqm_exec(struct ast_channel *chan, const char *data)
{
	int res=-1;
	char *parse, *temppos = NULL;

	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(interface);
		AST_APP_ARG(options);
	);


	if (ast_strlen_zero(data)) {
		ast_log(LOG_WARNING, "RemoveQueueMember requires an argument (queuename[,interface[,options]])\n");
		return -1;
	}

	parse = ast_strdupa(data);

	AST_STANDARD_APP_ARGS(args, parse);

	if (ast_strlen_zero(args.interface)) {
		args.interface = ast_strdupa(chan->name);
		temppos = strrchr(args.interface, '-');
		if (temppos)
			*temppos = '\0';
	}

	ast_debug(1, "queue: %s, member: %s\n", args.queuename, args.interface);

	switch (remove_from_queue(args.queuename, args.interface, chan->uniqueid)) {
	case RES_OKAY:
		ast_log(LOG_NOTICE, "Removed interface '%s' from queue '%s'\n", args.interface, args.queuename);
		pbx_builtin_setvar_helper(chan, "RQMSTATUS", "REMOVED");
		res = 0;
		break;
	case RES_EXISTS:
		ast_debug(1, "Unable to remove interface '%s' from queue '%s': Not there\n", args.interface, args.queuename);
		pbx_builtin_setvar_helper(chan, "RQMSTATUS", "NOTINQUEUE");
		res = 0;
		break;
	case RES_NOSUCHQUEUE:
		ast_log(LOG_WARNING, "Unable to remove interface from queue '%s': No such queue\n", args.queuename);
		pbx_builtin_setvar_helper(chan, "RQMSTATUS", "NOSUCHQUEUE");
		res = 0;
		break;
	case RES_NOT_DYNAMIC:
		ast_log(LOG_WARNING, "Unable to remove interface from queue '%s': '%s' is not a dynamic member\n", args.queuename, args.interface);
		pbx_builtin_setvar_helper(chan, "RQMSTATUS", "NOTDYNAMIC");
		res = 0;
		break;
	}

	return res;
}

/*! \brief AddQueueMember application */
static int aqm_exec(struct ast_channel *chan, const char *data)
{
	struct ast_config *mcfg;
	struct ast_category *mcat;
	struct call_queue *q;
	int res=-1;
	char *parse, *temppos = NULL;
	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(interface);
		AST_APP_ARG(penalty);
		AST_APP_ARG(paused);
		AST_APP_ARG(membername);
		AST_APP_ARG(state_interface);
		AST_APP_ARG(callinuse);
	);

	if (ast_strlen_zero(data)) {
		ast_log(LOG_WARNING, "AddQueueMember requires an argument (queuename[,interface[,penalty[,paused[,membername[,stateinterface[,callinuse]]]]])\n");
		return -1;
	}

	parse = ast_strdupa(data);

	AST_STANDARD_APP_ARGS(args, parse);

	if (ast_strlen_zero(args.interface)) {
		args.interface = ast_strdupa(chan->name);
		temppos = strrchr(args.interface, '-');
		if (temppos) {
			*temppos = '\0';
		}
	}

	mcfg = ast_config_new();
	mcat = ast_category_new(args.interface, chan->name, -1);

	if (!mcfg || !mcat) {
		ast_log(LOG_ERROR, "Out of memory adding interface %s to queue %s\n", args.interface, args.queuename);
		return res;
	} else {
		ast_category_append(mcfg, mcat);
	}

	if (!(q = load_realtime_queue(args.queuename, NULL))) {
		ast_log(LOG_WARNING, "Unable to add interface to queue '%s': No such queue\n", args.queuename);
		pbx_builtin_setvar_helper(chan, "AQMSTATUS", "NOSUCHQUEUE");
		return 0;
	}

	add_var_to_cat(mcat, "penalty", args.penalty);
	add_var_to_cat(mcat, "paused", args.paused);
	add_var_to_cat(mcat, "membername", args.membername);
	add_var_to_cat(mcat, "state_interface", args.state_interface);
	add_var_to_cat(mcat, "callinuse", args.callinuse);

	switch (handle_member_record(q, args.interface, mcfg, QUEUE_ADD_MEMBER_DYNAMIC, chan->uniqueid)) {
	case RES_OKAY:
		ast_log(LOG_NOTICE, "Added interface '%s' to queue '%s'\n", args.interface, args.queuename);
		pbx_builtin_setvar_helper(chan, "AQMSTATUS", "ADDED");
		res = 0;
		/* write out to db */
		if (queue_persistent_members) {
			dump_queue_members(q);
		}
		break;
	case RES_EXISTS:
		ast_log(LOG_WARNING, "Unable to add interface '%s' to queue '%s': Already there\n", args.interface, args.queuename);
		pbx_builtin_setvar_helper(chan, "AQMSTATUS", "MEMBERALREADY");
		res = 0;
		break;
	case RES_OUTOFMEMORY:
		ast_log(LOG_ERROR, "Out of memory adding interface %s to queue %s\n", args.interface, args.queuename);
		break;
	case RES_ERROR:
		ast_log(LOG_ERROR, "Error adding interface %s to queue %s\n", args.interface, args.queuename);
		break;
	}

	ao2_ref(q, -1);
	ast_config_destroy(mcfg);
	return res;
}

/*! \brief QueueLog application */
static int ql_exec(struct ast_channel *chan, const char *data)
{
	char *parse;

	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(uniqueid);
		AST_APP_ARG(membername);
		AST_APP_ARG(event);
		AST_APP_ARG(params);
	);

	if (ast_strlen_zero(data)) {
		ast_log(LOG_WARNING, "QueueLog requires arguments (queuename,uniqueid,membername,event[,additionalinfo]\n");
		return -1;
	}

	parse = ast_strdupa(data);

	AST_STANDARD_APP_ARGS(args, parse);

	if (ast_strlen_zero(args.queuename) || ast_strlen_zero(args.uniqueid)
	    || ast_strlen_zero(args.membername) || ast_strlen_zero(args.event)) {
		ast_log(LOG_WARNING, "QueueLog requires arguments (queuename,uniqueid,membername,event[,additionalinfo])\n");
		return -1;
	}

	ast_queue_log(args.queuename, args.uniqueid, args.membername, args.event, 
		"%s", args.params ? args.params : "");

	return 0;
}

/*!\brief The starting point for all queue calls
 *
 * The process involved here is to
 * 1. Parse the options specified in the call to Queue()
 * 2. Join the queue
 * 3. Wait in a loop until it is our turn to try calling a queue member
 * 4. Attempt to call a queue member
 * 5. If 4. did not result in a bridged call, then check for between
 *    call options such as periodic announcements etc.
 * 6. Try 4 again unless some condition (such as an expiration time) causes us to 
 *    exit the queue.
 */
static int queue_exec(struct ast_channel *chan, const char *data)
{
	int res=-1;
	int ringing=0;
	const char *user_priority;
	const char *max_penalty_str;
	const char *min_penalty_str;
	int prio;
	int qcontinue = 0;
	int max_penalty, min_penalty;
	enum queue_result reason = QUEUE_UNKNOWN;
	/* whether to exit Queue application after the timeout hits */
	int tries = 0;
	int noption = 0;
	char *parse;
	int makeannouncement = 0;
	int position = 0;
	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(options);
		AST_APP_ARG(url);
		AST_APP_ARG(announceoverride);
		AST_APP_ARG(queuetimeoutstr);
		AST_APP_ARG(agi);
		AST_APP_ARG(macro);
		AST_APP_ARG(gosub);
		AST_APP_ARG(rule);
		AST_APP_ARG(position);
	);
	/* Our queue entry */
	struct queue_ent qe = { 0 };

	if (ast_strlen_zero(data)) {
		ast_log(LOG_WARNING, "Queue requires an argument: queuename[,options[,URL[,announceoverride[,timeout[,agi[,macro[,gosub[,rule[,position]]]]]]]]]\n");
		return -1;
	}

	parse = ast_strdupa(data);
	AST_STANDARD_APP_ARGS(args, parse);

	if (ast_strlen_zero(args.queuename)) {
		ast_log(AST_LOG_ERROR, "Queuename not specified\n");
		return -1;
	}

	/* Setup our queue entry */
	qe.start = ast_tvnow();

	/* set the expire time based on the supplied timeout; */
	if (!ast_strlen_zero(args.queuetimeoutstr)) {
		qe.expire = qe.start;
		qe.expire.tv_sec += atoi(args.queuetimeoutstr);
	} else {
		qe.expire = ast_tv(0, 0);
	}

	/* Get the priority from the variable ${QUEUE_PRIO} */
	ast_channel_lock(chan);
	user_priority = pbx_builtin_getvar_helper(chan, "QUEUE_PRIO");
	if (user_priority) {
		if (sscanf(user_priority, "%30d", &prio) == 1) {
			ast_debug(1, "%s: Got priority %d from ${QUEUE_PRIO}.\n", chan->name, prio);
		} else {
			ast_log(LOG_WARNING, "${QUEUE_PRIO}: Invalid value (%s), channel %s.\n",
				user_priority, chan->name);
			prio = 0;
		}
	} else {
		ast_debug(3, "NO QUEUE_PRIO variable found. Using default.\n");
		prio = 0;
	}

	/* Get the maximum penalty from the variable ${QUEUE_MAX_PENALTY} */

	if ((max_penalty_str = pbx_builtin_getvar_helper(chan, "QUEUE_MAX_PENALTY"))) {
		if (sscanf(max_penalty_str, "%30d", &max_penalty) == 1) {
			ast_debug(1, "%s: Got max penalty %d from ${QUEUE_MAX_PENALTY}.\n", chan->name, max_penalty);
		} else {
			ast_log(LOG_WARNING, "${QUEUE_MAX_PENALTY}: Invalid value (%s), channel %s.\n",
				max_penalty_str, chan->name);
			max_penalty = 0;
		}
	} else {
		max_penalty = 0;
	}

	if ((min_penalty_str = pbx_builtin_getvar_helper(chan, "QUEUE_MIN_PENALTY"))) {
		if (sscanf(min_penalty_str, "%30d", &min_penalty) == 1) {
			ast_debug(1, "%s: Got min penalty %d from ${QUEUE_MIN_PENALTY}.\n", chan->name, min_penalty);
		} else {
			ast_log(LOG_WARNING, "${QUEUE_MIN_PENALTY}: Invalid value (%s), channel %s.\n",
				min_penalty_str, chan->name);
			min_penalty = 0;
		}
	} else {
		min_penalty = 0;
	}
	ast_channel_unlock(chan);

	if (args.options && (strchr(args.options, 'r')))
		ringing = 1;

	if (ringing != 1 && args.options && (strchr(args.options, 'R'))) {
		qe.ring_when_ringing = 1;
	}

	if (args.options && (strchr(args.options, 'c')))
		qcontinue = 1;

	if (args.position) {
		position = atoi(args.position);
		if (position < 0) {
			ast_log(LOG_WARNING, "Invalid position '%s' given for call to queue '%s'. Assuming no preference for position\n", args.position, args.queuename);
			position = 0;
		}
	}

	ast_debug(1, "queue: %s, options: %s, url: %s, announce: %s, expires: %ld, priority: %d\n",
		args.queuename, args.options, args.url, args.announceoverride, (long)qe.expire.tv_sec, prio);

	qe.chan = chan;
	qe.prio = prio;
	qe.max_penalty = max_penalty;
	qe.min_penalty = min_penalty;
	qe.last_pos_said = 0;
	qe.last_pos = ast_tv(0, 0);
	qe.last_pannounce_time = ast_tvnow();
	qe.last_periodic_announce_sound = 0;
	qe.valid_digits = 0;

	qe.attempts = ao2_container_alloc(MAX_QUEUE_BUCKETS, callattempt_hash_fn, callattempt_watched_cb);

	if (join_queue(args.queuename, &qe, &reason, position)) {
		ast_log(LOG_WARNING, "Unable to join queue '%s'\n", args.queuename);
		set_queue_result(chan, reason);
		return 0;
	}
	ast_queue_log(args.queuename, chan->uniqueid, "NONE", "ENTERQUEUE", "%s|%s|%d",
		S_OR(args.url, ""),
		S_COR(chan->caller.id.number.valid, chan->caller.id.number.str, ""),
		qe.opos);
check_turns:
	if (ringing) {
		ast_indicate(chan, AST_CONTROL_RINGING);
	} else {
		ast_moh_start(chan, qe.parent->moh, NULL);
	}

	/* This is the wait loop for callers 2 through maxlen */
	res = wait_our_turn(&qe, ringing, &reason);
	if (res) {
		goto stop;
	}

	makeannouncement = 0;

	for (;;) {
		/* This is the wait loop for the head caller*/
		/* To exit, they may get their call answered; */
		/* they may dial a digit from the queue context; */
		/* or, they may timeout. */

		/* Leave if we have exceeded our queuetimeout */
		if (!ast_tvzero(qe.expire) && (ast_tvcmp(ast_tvnow(), qe.expire) >= 0)) {
			record_abandoned(&qe);
			reason = QUEUE_TIMEOUT;
			res = 0;
			ast_queue_log(args.queuename, chan->uniqueid,"NONE", "EXITWITHTIMEOUT", "%d||%ld",
				qe.pos, (long)ast_tvdiff_sec(ast_tvnow(), qe.start));
			break;
		}

		/* Make a position announcement, if enabled */
		if (makeannouncement && qe.parent->announcefrequency &&
		    say_position(&qe,ringing)) {
			goto stop;
		}
		makeannouncement = 1;

		/* Make a periodic announcement, if enabled */
		if (qe.parent->periodicannouncefrequency &&
		     say_periodic_announcement(&qe,ringing)) {
				goto stop;
		}

		/* Leave if we have exceeded our queuetimeout */
		if (!ast_tvzero(qe.expire) && (ast_tvcmp(ast_tvnow(), qe.expire) >= 0)) {
			record_abandoned(&qe);
			reason = QUEUE_TIMEOUT;
			res = 0;
			ast_queue_log(args.queuename, chan->uniqueid,"NONE", "EXITWITHTIMEOUT", "%d|%d|%ld",
				qe.pos, qe.opos, (long)ast_tvdiff_sec(ast_tvnow(), qe.start));
			break;
		}

		/* see if we need to move to the next penalty level for this queue */
		while (qe.pr && (ast_tvdiff_sec(ast_tvnow(), qe.start) >= qe.pr->time)) {
			update_qe_rule(&qe);
		}

		/* reload realtime members incase i have gained or lost a few */
		rt_load_member_config(qe.parent);

		/* Try calling all queue members for 'timeout' seconds */
		res = try_calling(&qe, args.options, args.announceoverride, args.url, &tries, &noption, args.agi, args.macro, args.gosub, ringing);
		if (res) {
			goto stop;
		}

		if (get_member_status(&qe, 0)) {
			record_abandoned(&qe);
			reason = QUEUE_LEAVEEMPTY;
			ast_queue_log(args.queuename, chan->uniqueid, "NONE", "EXITEMPTY", "%d|%d|%ld", qe.pos, qe.opos, (long)ast_tvdiff_sec(ast_tvnow(), qe.start));
			res = 0;
			break;
		}

		/* exit after 'timeout' cycle if 'n' option enabled */
		if (noption && tries >= ao2_container_count(qe.parent->data->members)) {
			ast_verb(3, "Exiting on time-out cycle\n");
			ast_queue_log(args.queuename, chan->uniqueid,"NONE", "EXITWITHTIMEOUT", "%d|%d|%ld",
				qe.pos, qe.opos, (long)ast_tvdiff_sec(ast_tvnow(), qe.start));
			record_abandoned(&qe);
			reason = QUEUE_TIMEOUT;
			res = 0;
			break;
		}

		/* Leave if we have exceeded our queuetimeout */
		if (!ast_tvzero(qe.expire) && (ast_tvcmp(ast_tvnow(), qe.expire) >= 0)) {
			record_abandoned(&qe);
			reason = QUEUE_TIMEOUT;
			res = 0;
			ast_queue_log(args.queuename, chan->uniqueid,"NONE", "EXITWITHTIMEOUT", "%d|%d|%ld",
				qe.pos, qe.opos, (long)ast_tvdiff_sec(ast_tvnow(), qe.start));
			break;
		}

		/* OK, we didn't get anybody; wait for 'retry' seconds; may get a digit to exit with */
		res = wait_a_bit(&qe);
		if (res)
			goto stop;

		/* Since this is a priority queue and
		 * it is not sure that we are still at the head
		 * of the queue, go and check for our turn again.
		 */
		if (!is_our_turn(&qe)) {
			ast_debug(1, "Darn priorities, going back in queue (%s)!\n", qe.chan->name);
			goto check_turns;
		}
	}

stop:
	if (res) {
		if (res < 0) {
			if (!qe.handled) {
				record_abandoned(&qe);
				ast_queue_log(args.queuename, chan->uniqueid, "NONE", "ABANDON",
					"%d|%d|%ld", qe.pos, qe.opos,
					(long)ast_tvdiff_sec(ast_tvnow(), qe.start));
				res = -1;
			} else if (qcontinue) {
				reason = QUEUE_CONTINUE;
				res = 0;
			}
		} else if (qe.valid_digits) {
			ast_queue_log(args.queuename, chan->uniqueid, "NONE", "EXITWITHKEY",
				"%s|%d", qe.digits, qe.pos);
		}
	}

	/* Don't allow return code > 0 */
	if (res >= 0) {
		res = 0;	
		if (ringing) {
			ast_indicate(chan, -1);
		} else {
			ast_moh_stop(chan);
		}			
		ast_stopstream(chan);
	}

	set_queue_variables(qe.parent, qe.chan);

	leave_queue(&qe);
	if (reason != QUEUE_UNKNOWN)
		set_queue_result(chan, reason);

	if (qe.parent) {
		/* every queue_ent is given a reference to it's parent call_queue when it joins the queue.
		 * This ref must be taken away right before the queue_ent is destroyed.  In this case
		 * the queue_ent is about to be returned on the stack */
		ao2_ref(qe.parent, -1);
		qe.parent = NULL;
	}

	ao2_callback(qe.attempts, OBJ_UNLINK | OBJ_NODATA | OBJ_MULTIPLE, NULL, NULL);
	ao2_ref(qe.attempts, -1);

	if (qe.pr) {
		ao2_ref(qe.pr, -1);
	}

	if (qe.rules) {
		ao2_ref(qe.rules, -1);
	}

	return res;
}

/*!
 * \brief create interface var with all queue details.
 * \retval 0 on success
 * \retval -1 on error
*/
static int queue_function_var(struct ast_channel *chan, const char *cmd, char *data, char *buf, size_t len)
{
	int res = -1;
	struct call_queue *q;

	char interfacevar[256] = "";
	float sl = 0;

	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "%s requires an argument: queuename\n", cmd);
		return -1;
	}

	if ((q = load_realtime_queue(data, NULL))) {
		if (q->setqueuevar) {
			sl = 0;
			res = 0;

			ao2_lock(q->data);
			if (q->data->callscompleted > 0) {
				sl = 100 * ((float) q->data->callscompletedinsl / (float) q->data->callscompleted);
			}

			snprintf(interfacevar, sizeof(interfacevar),
				"QUEUEMAX=%d,QUEUESTRATEGY=%s,QUEUECALLS=%d,QUEUEHOLDTIME=%d,QUEUETALKTIME=%d,QUEUECOMPLETED=%d,QUEUEABANDONED=%d,QUEUESRVLEVEL=%d,QUEUESRVLEVELPERF=%2.1f",
				q->maxlen, int2strat(q->strategy), q->data->count, q->data->holdtime, q->data->talktime, q->data->callscompleted, q->data->callsabandoned,  q->servicelevel, sl);

			ao2_unlock(q->data);
			pbx_builtin_setvar_multiple(chan, interfacevar);
		}
		ao2_t_ref(q, -1, "Done with QUEUE() function");
	} else {
		ast_log(LOG_WARNING, "queue %s was not found\n", data);
	}

	snprintf(buf, len, "%d", res);

	return 0;
}

/*!
 * \brief Check if a given queue exists
 *
 */
static int queue_function_exists(struct ast_channel *chan, const char *cmd, char *data, char *buf, size_t len)
{
	struct call_queue *q;

	buf[0] = '\0';

	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "%s requires an argument: queuename\n", cmd);
		return -1;
	}
	q = load_realtime_queue(data, NULL);
	snprintf(buf, len, "%d", q != NULL? 1 : 0);
	if (q) {
		ao2_t_ref(q, -1, "Done with temporary reference in QUEUE_EXISTS()");
	}

	return 0;
}

/*!
 * \brief Get number either busy / free / ready or total members of a specific queue
 * \brief Get or set member properties penalty / paused / callinuse
 * \retval number of members (busy / free / ready / total) or member info (penalty / paused / callinuse)
 * \retval -1 on error
*/
static int queue_function_mem_read(struct ast_channel *chan, const char *cmd, char *data, char *buf, size_t len)
{
	int count = 0;
	int status;
	struct member *m;
	struct ao2_iterator mem_iter;
	struct call_queue *q;
	struct ast_flags qflags = {QUEUE_RELOAD_MEMBER};

	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(option);
		AST_APP_ARG(interface);
	);
	/* Make sure the returned value on error is zero length string. */
	buf[0] = '\0';

	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "Missing required argument. %s(<queuename>,<option>[<interface>])\n", cmd);
		return -1;
	}

	AST_STANDARD_APP_ARGS(args, data);
	if ((q = load_realtime_queue(args.queuename, &qflags))) {
		if (!strcasecmp(args.option, "logged")) {
			mem_iter = ao2_iterator_init(q->data->members, 0);
			while ((m = ao2_iterator_next(&mem_iter))) {
				/* Count the agents who are logged in and reachable */
				ao2_lock(m);
				status = get_device_status(m);
				if ((status != AST_DEVICE_UNAVAILABLE) && (status != AST_DEVICE_INVALID)) {
					count++;
				}
				ao2_unlock(m);
				ao2_ref(m, -1);
			}
			ao2_iterator_destroy(&mem_iter);
		} else if (!strcasecmp(args.option, "free")) {
			mem_iter = ao2_iterator_init(q->data->members, 0);
			while ((m = ao2_iterator_next(&mem_iter))) {
				ao2_lock(m);
				/* Count the agents who are logged in and not presently on calls */
				status = get_device_status(m);
				if ((status == AST_DEVICE_NOT_INUSE) && (!m->paused)) {
					count++;
				}
				ao2_unlock(m);
				ao2_ref(m, -1);
			}
			ao2_iterator_destroy(&mem_iter);
		} else if (!strcasecmp(args.option, "ready")) {
			mem_iter = ao2_iterator_init(q->data->members, 0);
			while ((m = ao2_iterator_next(&mem_iter))) {
				ao2_lock(m);
				/* Count the agents who are logged in, not on a call, not paused and not wrapping up */
				status = get_device_status(m);
				if ((status == AST_DEVICE_NOT_INUSE) && !m->paused &&
				    !(!ast_tvzero(m->lastcall) && m->lastwrapup &&
				      (ast_tvdiff_sec(ast_tvnow(), m->lastcall) <= m->lastwrapup))) {
					count++;
				}
				ao2_unlock(m);
				ao2_ref(m, -1);
			}
			ao2_iterator_destroy(&mem_iter);
		} else if (!strcasecmp(args.option, "count") || ast_strlen_zero(args.option)) {
			count = ao2_container_count(q->data->members);
		} else if (!strcasecmp(args.option, "penalty") && !ast_strlen_zero(args.interface) &&
			   ((m = interface_exists(q, args.interface)))) {
			ao2_lock(m);
			count = m->penalty;
			ao2_unlock(m);
			ao2_ref(m, -1);
		} else if (!strcasecmp(args.option, "paused") && !ast_strlen_zero(args.interface) &&
			   ((m = interface_exists(q, args.interface)))) {
			ao2_lock(m);
			count = m->paused;
			ao2_unlock(m);
			ao2_ref(m, -1);
		} else if (!strcasecmp(args.option, "callinuse") && !ast_strlen_zero(args.interface) &&
			   ((m = interface_exists(q, args.interface)))) {
			ao2_lock(m);
			count = m->callinuse;
			ao2_unlock(m);
			ao2_ref(m, -1);
		} else {
			ast_log(LOG_ERROR, "Unknown option %s provided to %s, valid values are: "
				"logged, free, ready, count, penalty, paused, ignorebusy\n", args.option, cmd);
		}
		ao2_t_ref(q, -1, "Done with temporary reference in QUEUE_MEMBER()");
	} else {
		ast_log(LOG_WARNING, "queue %s was not found\n", args.queuename);
	}

	snprintf(buf, len, "%d", count);

	return 0;
}

/*! \brief Dialplan function QUEUE_MEMBER() Sets the members penalty / paused / callinuse. */
static int queue_function_mem_write(struct ast_channel *chan, const char *cmd, char *data, const char *value)
{
	int memvalue;
	struct call_queue *q;
	struct member *m;
	int ret = 0;

	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(option);
		AST_APP_ARG(interface);
	);

	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "Missing argument. QUEUE_MEMBER(<queuename>,<option>,<interface>)\n");
		return -1;
	}

	AST_STANDARD_APP_ARGS(args, data);

	if (args.argc < 2) {
		ast_log(LOG_ERROR, "Missing argument. QUEUE_MEMBER(<queuename>,<option>[,<interface>])\n");
		return -1;
	}

	if (ast_strlen_zero(args.interface) && ast_strlen_zero(args.option)) {
		ast_log (LOG_ERROR, "<interface> and <option> parameter's can't be null\n");
		return -1;
	}

	if (sscanf(value, "%30d", &memvalue) != 1) {
		ast_log(AST_LOG_ERROR, "Failed to read value from %s\n", value);
		return -1;
	}

	if (!strcasecmp(args.option, "penalty")) {
		/* if queuename = NULL then penalty will be set for interface in all the queues.*/
		if (set_member_penalty(args.queuename, args.interface, memvalue)) {
			ast_log(LOG_ERROR, "Invalid interface, queue or penalty\n");
			return -1;
		}
	} else if (!strcasecmp(args.option, "paused")) {
		/* if queuename = NULL then paused will be set for interface in all the queues.*/
		if (set_member_paused(args.queuename, args.interface, NULL, memvalue)) {
			ast_log(LOG_ERROR, "Invalid interface or queue\n");
			return -1;
		}
	} else if (!ast_strlen_zero(args.queuename)) {
		if (!(q = load_realtime_queue(args.queuename, NULL))) {
			ast_log(LOG_ERROR, "Invalid queue %s\n", args.queuename);
			return -1;
		}
		if (!(m = interface_exists(q, args.interface))) {
			ao2_ref(q, -1);
			ast_log(LOG_ERROR, "Invalid member %s queue %s\n", args.interface, args.queuename);
			return -1;
		}
		ao2_lock(m);
		if (!strcasecmp(args.option, "callinuse")) {
			m->callinuse = (memvalue) ? 1 : 0;
		} else {
			ast_log(LOG_ERROR, "Invalid option, only penalty , paused or callinuse are valid\n");
			ret = -1;
		}

		/* update the DB data */
		if (!ret && m->realtime) {
			update_realtime_member_field(m, q->name, args.option, value);
			ao2_unlock(m);
		} else if (!ret && m->dynamic && queue_persistent_members) {
			ao2_unlock(m);
			dump_queue_members(q);
		}

		ao2_ref(m, -1);
		ao2_ref(q, -1);
        } else {
		ast_log(LOG_ERROR, "Invalid queue\n");
		return -1;
	}
	return ret;
}

/*! \brief Dialplan function QUEUE_WAITING_COUNT() Get number callers waiting in a specific queue */
static int queue_function_queuewaitingcount(struct ast_channel *chan, const char *cmd, char *data, char *buf, size_t len)
{
	int count = 0;
	struct call_queue *q;
	struct ast_variable *var = NULL;

	buf[0] = '\0';

	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "QUEUE_WAITING_COUNT requires an argument: queuename\n");
		return -1;
	}

	if ((q = ao2_t_find(queues, data, 0, "Find for QUEUE_WAITING_COUNT()"))) {
		ao2_lock(q->data);
		count = q->data->count;
		ao2_unlock(q->data);
		ao2_t_ref(q, -1, "Done with reference in QUEUE_WAITING_COUNT()");
	} else if ((var = ast_load_realtime("queues", "name", data, SENTINEL))) {
		/* if the queue is realtime but was not found in memory, this
		 * means that the queue had been deleted from memory since it was
		 * "dead." This means it has a 0 waiting count
		 */
		count = 0;
		ast_variables_destroy(var);
	} else
		ast_log(LOG_WARNING, "queue %s was not found\n", data);

	snprintf(buf, len, "%d", count);

	return 0;
}

/*! \brief Dialplan function QUEUE_MEMBER_LIST() Get list of members in a specific queue */
static int queue_function_queuememberlist(struct ast_channel *chan, const char *cmd, char *data, char *buf, size_t len)
{
	struct call_queue *q;
	struct member *m;
	int buflen = 0, count = 0;
	struct ao2_iterator mem_iter;
	struct ast_flags qflags = {QUEUE_RELOAD_MEMBER};

	/* Ensure an otherwise empty list doesn't return garbage */
	buf[0] = '\0';

	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "QUEUE_MEMBER_LIST requires an argument: queuename\n");
		return -1;
	}

	if ((q = load_realtime_queue(data, &qflags))) {
		ast_log(LOG_WARNING, "queue %s was not found\n", data);
		return -1;
	}

	mem_iter = ao2_iterator_init(q->data->members, 0);
	while ((m = ao2_iterator_next(&mem_iter))) {
		/* strcat() is always faster than printf() */
		if (count++) {
			strncat(buf + buflen, ",", len - buflen - 1);
			buflen++;
		}
		strncat(buf + buflen, m->interface, len - buflen - 1);
		buflen += strlen(m->interface);
		/* Safeguard against overflow (negative length) */
		if (buflen >= len - 2) {
			ao2_ref(m, -1);
			ast_log(LOG_WARNING, "Truncating list\n");
			break;
		}
		ao2_ref(m, -1);
	}
	ao2_iterator_destroy(&mem_iter);
	ao2_t_ref(q, -1, "Done with QUEUE_MEMBER_LIST()");

	/* We should already be terminated, but let's make sure. */
	buf[len - 1] = '\0';

	return 0;
}

/*! \brief Dialplan function QUEUE_MEMBER_PENALTY() Gets the members penalty. */
static int queue_function_memberpenalty_read(struct ast_channel *chan, const char *cmd, char *data, char *buf, size_t len)
{
	struct member *m;
	struct call_queue *q;
	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(interface);
	);
	/* Make sure the returned value on error is NULL. */
	buf[0] = '\0';

	ast_log(LOG_NOTICE, "The function QUEUE_MEMBER_PENALTY has been deprecated in favor of the QUEUE_MEMBER function and will not be in further releases.\n");

	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "Missing argument. QUEUE_MEMBER_PENALTY(<queuename>,<interface>)\n");
		return -1;
	}

	AST_STANDARD_APP_ARGS(args, data);

	if (args.argc < 2) {
		ast_log(LOG_ERROR, "Missing argument. QUEUE_MEMBER_PENALTY(<queuename>,<interface>)\n");
		return -1;
	}

	if (!(q = load_realtime_queue(args.queuename, NULL))) {
		ast_log(AST_LOG_WARNING, "Queue %s does not exist\n", args.queuename);
		return -1;
	}

	if (!(m = interface_exists(q, args.interface))) {
		ast_log(AST_LOG_WARNING, "Member %s is not available on queue %s\n", args.interface, args.queuename);
		ao2_ref(q, -1);
		return -1;
	}

	ao2_ref(q, -1);
	ao2_lock(m);
	snprintf (buf, len, "%d", m->penalty);
	ao2_unlock(m);
	ao2_ref(m, -1);

	return 0;
}

/*! \brief Dialplan function QUEUE_MEMBER_PENALTY() Sets the members penalty. */
static int queue_function_memberpenalty_write(struct ast_channel *chan, const char *cmd, char *data, const char *value)
{
	int penalty;
	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(queuename);
		AST_APP_ARG(interface);
	);

	if (ast_strlen_zero(data)) {
		ast_log(LOG_ERROR, "Missing argument. QUEUE_MEMBER_PENALTY(<queuename>,<interface>)\n");
		return -1;
	}

	AST_STANDARD_APP_ARGS(args, data);

	if (args.argc < 2) {
		ast_log(LOG_ERROR, "Missing argument. QUEUE_MEMBER_PENALTY(<queuename>,<interface>)\n");
		return -1;
	}

	penalty = atoi(value);

	if (ast_strlen_zero(args.interface)) {
		ast_log (LOG_ERROR, "<interface> parameter can't be null\n");
		return -1;
	}

	/* if queuename = NULL then penalty will be set for interface in all the queues. */
	if (set_member_penalty(args.queuename, args.interface, penalty)) {
		ast_log(LOG_ERROR, "Invalid interface, queue or penalty\n");
		return -1;
	}

	return 0;
}

static struct ast_custom_function queueexists_function = {
	.name = "QUEUE_EXISTS",
	.read = queue_function_exists,
};

static struct ast_custom_function queuevar_function = {
	.name = "QUEUE_VARIABLES",
	.read = queue_function_var,
};

static struct ast_custom_function queuemembercount_function = {
	.name = "QUEUE_MEMBER",
	.read = queue_function_mem_read,
	.write = queue_function_mem_write,
};

static struct ast_custom_function queuewaitingcount_function = {
	.name = "QUEUE_WAITING_COUNT",
	.read = queue_function_queuewaitingcount,
};

static struct ast_custom_function queuememberlist_function = {
	.name = "QUEUE_MEMBER_LIST",
	.read = queue_function_queuememberlist,
};

static struct ast_custom_function queuememberpenalty_function = {
	.name = "QUEUE_MEMBER_PENALTY",
	.read = queue_function_memberpenalty_read,
	.write = queue_function_memberpenalty_write,
};

/*!
 * \brief ao2 callback to delete priority rules
 */
static void delete_priority_rule(void *data)
{
	struct rule_list *rule = data;

	ao2_callback(rule->rules, OBJ_UNLINK | OBJ_NODATA | OBJ_MULTIPLE, NULL, NULL);
	ao2_ref(rule->rules, -1);
}

/*! \brief Reload the rules defined in queuerules.conf
 *
 * \param reload If 1, then only process queuerules.conf if the file
 * has changed since the last time we inspected it.
 * \return Always returns AST_MODULE_LOAD_SUCCESS
 */
static int reload_queue_rules(int reload)
{
	struct ast_config *cfg;
	struct rule_list *new_rl;
	char *rulecat = NULL;
	struct ast_variable *rulevar = NULL;
	struct ast_flags config_flags = { reload ? CONFIG_FLAG_FILEUNCHANGED : 0 };

	if (!(cfg = ast_config_load("queuerules.conf", config_flags))) {
		ast_log(LOG_NOTICE, "No queuerules.conf file found, queues will not follow penalty rules\n");
		return AST_MODULE_LOAD_SUCCESS;
	} else if (cfg == CONFIG_STATUS_FILEUNCHANGED) {
		ast_log(LOG_NOTICE, "queuerules.conf has not changed since it was last loaded. Not taking any action.\n");
		return AST_MODULE_LOAD_SUCCESS;
	} else if (cfg == CONFIG_STATUS_FILEINVALID) {
		ast_log(LOG_ERROR, "Config file queuerules.conf is in an invalid format.  Aborting.\n");
		return AST_MODULE_LOAD_SUCCESS;
	}

	/* unlink all objects they will be deleted when all refference to them is droped*/
	ao2_callback(rules, OBJ_UNLINK | OBJ_NODATA | OBJ_MULTIPLE, NULL, NULL);

	while ((rulecat = ast_category_browse(cfg, rulecat))) {
		if (!(new_rl = ao2_alloc(sizeof(*new_rl), delete_priority_rule))) {
			ast_config_destroy(cfg);
			return AST_MODULE_LOAD_FAILURE;
		} else {
			if (!(new_rl->rules = ao2_container_alloc(MAX_QUEUE_BUCKETS, penalty_hash_cb, NULL))) {
				ao2_ref(new_rl, -1);
				continue;
			}
			ast_copy_string(new_rl->name, rulecat, sizeof(new_rl->name));
			ao2_link(rules, new_rl);
			for (rulevar = ast_variable_browse(cfg, rulecat); rulevar; rulevar = rulevar->next) {
				if(!strcasecmp(rulevar->name, "penaltychange")) {
					insert_penaltychange(new_rl->rules, rulevar->value, rulevar->lineno);
				} else {
					ast_log(LOG_WARNING, "Don't know how to handle rule type '%s' on line %d\n", rulevar->name, rulevar->lineno);
				}
			}
		}
	}

	ast_config_destroy(cfg);

	return AST_MODULE_LOAD_SUCCESS;
}

/*! Set the global queue parameters as defined in the "general" section of queues.conf */
static void queue_set_global_params(struct ast_config *cfg)
{
	const char *general_val = NULL;
	queue_persistent_members = 0;
	if ((general_val = ast_variable_retrieve(cfg, "general", "persistentmembers"))) {
		queue_persistent_members = ast_true(general_val);
	}
	autofill_default = 0;
	if ((general_val = ast_variable_retrieve(cfg, "general", "autofill"))) {
		autofill_default = ast_true(general_val);
	}
	montype_default = 0;
	if ((general_val = ast_variable_retrieve(cfg, "general", "monitor-type"))) {
		if (!strcasecmp(general_val, "mixmonitor"))
			montype_default = 1;
	}
	update_cdr = 0;
	if ((general_val = ast_variable_retrieve(cfg, "general", "updatecdr"))) {
		update_cdr = ast_true(general_val);
	}
	shared_lastcall = 0;
	if ((general_val = ast_variable_retrieve(cfg, "general", "shared_lastcall"))) {
		shared_lastcall = ast_true(general_val);
	}
	negative_penalty_invalid = 0;
	if ((general_val = ast_variable_retrieve(cfg, "general", "negative_penalty_invalid"))) {
		negative_penalty_invalid = ast_true(general_val);
	}
	log_membername_as_agent = 0;
	if ((general_val = ast_variable_retrieve(cfg, "general", "log_membername_as_agent"))) {
		log_membername_as_agent = ast_true(general_val);
	}
}

/*! \brief reload information pertaining to a single member
 *
 * This function is called when a member = line is encountered in
 * queues.conf.
 *
 * \param memberdata The part after member = in the config file
 * \param q The queue to which this member belongs
 */
static struct ast_category *reload_single_member(const char *memberdata, struct call_queue *q)
{
	char *parse;
	struct ast_category *mcat;

	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(interface);
		AST_APP_ARG(penalty);
		AST_APP_ARG(membername);
		AST_APP_ARG(state_interface);
		AST_APP_ARG(paused);
		AST_APP_ARG(callinuse);
	);

	if (ast_strlen_zero(memberdata)) {
		ast_log(LOG_WARNING, "Empty queue member definition. Moving on!\n");
		return NULL;
	}

	/* Add a new member */
	parse = ast_strdupa(memberdata);

	AST_STANDARD_APP_ARGS(args, parse);

	if (!(mcat = ast_category_new(args.interface, "queues.conf", -1))) {
		ast_log(LOG_ERROR, "Out of memory adding interface %s to queue %s\n", args.interface, q->name);
		return NULL;
	}

	add_var_to_cat(mcat, "penalty", args.penalty);
	add_var_to_cat(mcat, "paused", args.paused);
	add_var_to_cat(mcat, "membername", args.membername);
	add_var_to_cat(mcat, "state_interface", args.state_interface);
	add_var_to_cat(mcat, "callinuse", args.callinuse);

	return mcat;
}

/*!
 * \brief ao2 callback to mark static members dead
 */
static int mark_static_member_dead(void *obj, void *arg, int flags)
{
	struct member *member = obj;

	if (!member->dynamic && !member->realtime) {
		member->dead = 1;
		return CMP_MATCH;
	}

	return 0;
}

/*!
 * \brief ao2 callback to delete static members marked dead
 */
static int kill_static_dead_members(void *obj, void *arg, int flags)
{
	struct member *member = obj;

	if (!member->dynamic && !member->realtime && member->dead) {
		return CMP_MATCH;
	}
	return 0;
}

/*! \brief Reload information pertaining to a particular queue
 *
 * Once we have isolated a queue within reload_queues, we call this. This will either
 * reload information for the queue or if we're just reloading member information, we'll just
 * reload that without touching other settings within the queue 
 *
 * \param cfg The configuration which we are reading
 * \param mask Tells us what information we need to reload
 * \param queuename The name of the queue we are reloading information from
 * \retval void
 */
static void reload_single_queue(struct ast_config *cfg, struct ast_flags *mask, const char *queuename)
{
	struct call_queue *q = NULL, *oldq = NULL;
	/*We're defining a queue*/
	const int queue_reload = ast_test_flag(mask, QUEUE_RELOAD_PARAMETERS);
	const int member_reload = ast_test_flag(mask, QUEUE_RELOAD_MEMBER);
	int prev_weight = 0;
	struct ast_variable *var;
	struct ast_config *mcfg = NULL;
	struct ast_category *mcat;
	const char *interface = NULL;

	if (!(oldq = ao2_find(queues, (char *)queuename, 0)) &&
	    (!queue_reload || (!(q = alloc_queue(queuename, 0))))) {
			/* Since we're not reloading queues, this means that we found a queue
			 * in the configuration file which we don't know about yet. Just return.
			 * or we could not alloc a new queue
			 */
			return;
	} else if (oldq && queue_reload) {
		prev_weight = oldq->weight ? 1 : 0;
		if (!(q = alloc_queue(queuename, 1))) {
			ast_log(AST_LOG_ERROR, "Failed to configure new queue object: reload aborted\n");
			ao2_ref(oldq, -1);
			return;
		}
	} else if (oldq) {
		q = oldq;
		oldq = NULL;
		q->dead = 0;
	}

	if (member_reload && !(mcfg = ast_config_new())) {
		ast_log(AST_LOG_ERROR, "Could not create member config for Queue %s\n",queuename);
	}

	for (var = ast_variable_browse(cfg, queuename); var; var = var->next) {
		if (mcfg && !strcasecmp(var->name, "member")) {
			if ((mcat = reload_single_member(var->value, q))) {
				ast_category_append(mcfg, mcat);
			}
		} else if (queue_reload) {
			queue_set_param(q, var->name, var->value, var->lineno, 1);
		}
	}

	if (queue_reload) {
		/* configure the queue members containers it must never change */
		if (!q->data->members && (q->strategy == QUEUE_STRATEGY_LINEAR || q->strategy == QUEUE_STRATEGY_RRORDERED)) {
			/* linear strategy depends on order, so we have to place all members in a single bucket */
			q->data->members = ao2_container_alloc(1, member_hash_fn, member_cmp_fn);
		} else if (!q->data->members) {
			q->data->members = ao2_container_alloc(37, member_hash_fn, member_cmp_fn);
		}

		/* At this point, we've determined if the queue has a weight, so update use_weight
		 * as appropriate
		 */
		if (!q->weight && prev_weight) {
			ast_atomic_fetchadd_int(&use_weight, -1);
		} else if (q->weight && !prev_weight) {
			ast_atomic_fetchadd_int(&use_weight, +1);
		}
	}

	if (mcfg) {
		ao2_callback(q->data->members, OBJ_NODATA | OBJ_MULTIPLE, mark_static_member_dead, NULL);
		while ((interface = ast_category_browse(mcfg, interface))) {
			handle_member_record(q, interface, mcfg, QUEUE_ADD_MEMBER_STATIC, "queues.conf");
		}
		/* Free remaining members marked as dead */
		ao2_callback(q->data->members, OBJ_NODATA | OBJ_MULTIPLE | OBJ_UNLINK, kill_static_dead_members, NULL);

		/* load the realtime agents*/
		rt_load_member_config(q);

		/* add persistent members to new queue*/
		if (queue_persistent_members) {
			pm_load_member_config(q);
		}

		ast_config_destroy(mcfg);
	}

	if (queue_reload && oldq) {
		ao2_lock(queues);
		ao2_find(queues, oldq, OBJ_UNLINK | OBJ_POINTER | OBJ_NODATA | OBJ_NOLOCK);
		ao2_link(queues, q);
		ao2_unlock(queues);
		ao2_ref(oldq, -1);
	} else if (queue_reload) {
		ao2_link(queues, q);
	}

	ao2_ref(q, -1);
}

/*!
 * \brief ao2 callback to mark static queues dead
 */
static int mark_queues_dead(void *obj, void *arg, int flags)
{
	struct call_queue *q = obj;
	const struct call_queue *q2 = arg;
	const char *queuename = (arg && (flags & OBJ_POINTER)) ? q2->name : arg;

	if (!q->realtime && (ast_strlen_zero(queuename) || !strcasecmp(queuename, q->name))) {
		q->dead = 1;
		return CMP_MATCH;
	}

	return 0;
}

/*!
 * \brief ao2 callback to delete queues marked dead
 */
static int kill_dead_queues(void *obj, void *arg, int flags)
{
	struct call_queue *q = obj;
	const struct call_queue *q2 = arg;
	const char *queuename = (arg && (flags & OBJ_POINTER)) ? q2->name : arg;

	if (q->dead && (ast_strlen_zero(queuename) || !strcasecmp(queuename, q->name))) {
		return CMP_MATCH;
	}

	return 0;
}

/*!
 * \brief ao2 callback to delete realtime members marked dead
 */
static int remove_all_members_from_queue(void *obj, void *arg, void *data, int flags)
{
	struct member *m = obj;
	const struct call_queue *q = data;

	if (!log_membername_as_agent) {
		ast_queue_log(q->name, "SHUTDOWN", m->interface, "REMOVEMEMBER", "%s", "");
	} else {
		ao2_lock(m);
		ast_queue_log(q->name, "SHUTDOWN", m->membername, "REMOVEMEMBER", "%s", "");
		ao2_unlock(m);
	}
	return CMP_MATCH;
}

/*!
 * \brief ao2 callback to delete realtime members marked dead
 */
static int remove_all_members(void *obj, void *arg, int flags)
{
	struct call_queue *q = obj;

	ao2_callback_data(q->data->members, OBJ_NODATA | OBJ_MULTIPLE | OBJ_UNLINK, remove_all_members_from_queue, NULL, q);
	return CMP_MATCH;
}

/*! \brief reload the queues.conf file
 *
 * This function reloads the information in the general section of the queues.conf
 * file and potentially more, depending on the value of mask.
 *
 * \param reload 0 if we are calling this the first time, 1 every other time
 * \param mask Gives flags telling us what information to actually reload
 * \param queuename If set to a non-zero string, then only reload information from
 * that particular queue. Otherwise inspect all queues
 * \retval -1 Failure occurred 
 * \retval 0 All clear!
 */
static int reload_queues(int reload, struct ast_flags *mask, const char *queuename)
{
	struct ast_config *cfg;
	char *cat;
	struct ast_flags config_flags = { reload ? CONFIG_FLAG_FILEUNCHANGED : 0 };
	const int queue_reload = ast_test_flag(mask, QUEUE_RELOAD_PARAMETERS);
	const int reload_members = ast_test_flag(mask, QUEUE_RELOAD_MEMBER);
	struct call_queue *q;
	int loaded = 0;

	if (!(cfg = ast_config_load("queues.conf", config_flags))) {
		ast_log(LOG_NOTICE, "No call queueing config file (queues.conf), so no call queues\n");
		return -1;
	} else if (cfg == CONFIG_STATUS_FILEINVALID) {
		ast_log(LOG_ERROR, "Config file queues.conf is in an invalid format.  Aborting.\n");
		return -1;
	}

	if (cfg != CONFIG_STATUS_FILEUNCHANGED) {
		/* Mark all queues as dead for the moment if we're reloading queues.
		 * For clarity, we could just be reloading members, in which case we don't want to mess
		 * with the other queue parameters at all*/
		if (queue_reload) {
			ao2_callback(queues, OBJ_NODATA | OBJ_MULTIPLE, mark_queues_dead, (char *) queuename);
		}

		/* Chug through config file */
		cat = NULL;
		while ((cat = ast_category_browse(cfg, cat)) ) {
			if (!strcasecmp(cat, "general") && queue_reload) {
				queue_set_global_params(cfg);
				continue;
			}
			if (ast_strlen_zero(queuename) || !strcasecmp(cat, queuename)) {
				loaded = 1;
				reload_single_queue(cfg, mask, cat);
			}
		}

		ast_config_destroy(cfg);
		/* Unref all the dead queues if we were reloading queues */
		if (queue_reload) {
			ao2_callback(queues, OBJ_NODATA | OBJ_MULTIPLE | OBJ_UNLINK, kill_dead_queues, (char *) queuename);
		}
	}

	/* reload realtime queues*/
	ast_set_flag(mask, QUEUE_RELOAD_REALTIME);
	if (ast_strlen_zero(queuename)) {
		load_all_realtime_queues(mask);
	} else if ((!loaded || reload_members) &&
		   (q = load_realtime_queue(queuename, mask))) {
		ao2_ref(q, -1);
	}
	return 0;
}

/*! \brief Facilitates resetting statistics for a queue
 *
 * This function actually does not reset any statistics, but
 * rather finds a call_queue struct which corresponds to the
 * passed-in queue name and passes that structure to the
 * clear_queue function. If no queuename is passed in, then
 * all queues will have their statistics reset.
 *
 * \param queuename The name of the queue to reset the statistics
 * for. If this is NULL or zero-length, then this means to reset
 * the statistics for all queues
 * \retval void
 */
static int clear_stats(const char *queuename)
{
	struct call_queue *q;
	struct ao2_iterator queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate through queues"))) {
		if (ast_strlen_zero(queuename) || !strcasecmp(q->name, queuename)) {
			ao2_lock(q->data);
			q->data->holdtime = 0;
			q->data->callscompleted = 0;
			q->data->callsabandoned = 0;
			q->data->callscompletedinsl = 0;
			q->data->talktime = 0;
			ao2_unlock(q->data);
			if (q->data->members) {
				ao2_callback(q->data->members, OBJ_NODATA, clear_queue_member_fn, NULL);
			}
		}
		ao2_t_ref(q, -1, "Done with iterator");
	}
	ao2_iterator_destroy(&queue_iter);
	return 0;
}

/*! \brief The command center for all reload operations
 *
 * Whenever any piece of queue information is to be reloaded, this function
 * is called. It interprets the flags set in the mask parameter and acts
 * based on how they are set.
 *
 * \param reload True if we are reloading information, false if we are loading
 * information for the first time.
 * \param mask A bitmask which tells the handler what actions to take
 * \param queuename The name of the queue on which we wish to take action
 * \retval 0 All reloads were successful
 * \retval non-zero There was a failure
 */
static int reload_handler(int reload, struct ast_flags *mask, const char *queuename)
{
	int res = 0;

	if (ast_test_flag(mask, QUEUE_RELOAD_RULES)) {
		res |= reload_queue_rules(reload);
	}
	if (ast_test_flag(mask, QUEUE_RESET_STATS)) {
		res |= clear_stats(queuename);
	}
	if (ast_test_flag(mask, (QUEUE_RELOAD_PARAMETERS | QUEUE_RELOAD_MEMBER))) {
		res |= reload_queues(reload, mask, queuename);
	}
	return res;
}

/*! \brief direct ouput to manager or cli with proper terminator */
static void do_print(struct mansession *s, int fd, const char *str)
{
	if (s)
		astman_append(s, "%s\r\n", str);
	else
		ast_cli(fd, "%s\n", str);
}

/*! 
 * \brief Show queue(s) status and statistics 
 * 
 * List the queues strategy, calls processed, members logged in,
 * other queue statistics such as avg hold time.
*/
static char *__queues_show(struct mansession *s, int fd, int argc, const char * const *argv)
{
	struct call_queue *q;
	struct ast_str *out = ast_str_alloca(240);
	int found = 0;
	struct timeval now = ast_tvnow();
	struct ao2_iterator queue_iter;
	struct ao2_iterator mem_iter;

	if (argc != 2 && argc != 3) {
		return CLI_SHOWUSAGE;
	}

	if ((argc == 3)	&&
	    (q = load_realtime_queue(argv[2], NULL))) {
		ao2_ref(q, -1);
	} else {
		load_all_realtime_queues(NULL);
	}

	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate through queues"))) {
		float sl;

		if (argc == 3 && strcasecmp(q->name, argv[2])) {
			ao2_t_ref(q, -1, "Done with iterator");
			continue;
		}
		found = 1;

		ao2_lock(q->data);

		ast_str_set(&out, 0, "%s has %d calls (max ", q->name, q->data->count);
		if (q->maxlen) {
			ast_str_append(&out, 0, "%d", q->maxlen);
		} else {
			ast_str_append(&out, 0, "unlimited");
		}
		sl = 0;
		if (q->data->callscompleted > 0) {
			sl = 100 * ((float) q->data->callscompletedinsl / (float) q->data->callscompleted);
		}
		ast_str_append(&out, 0, ") in '%s' strategy (%ds holdtime, %ds talktime), W:%d, C:%d, A:%d, SL:%2.1f%% within %ds",
			int2strat(q->strategy), q->data->holdtime, q->data->talktime, q->weight,
			q->data->callscompleted, q->data->callsabandoned,sl,q->servicelevel);
		do_print(s, fd, ast_str_buffer(out));
		ao2_unlock(q->data);

		if (!ao2_container_count(q->data->members)) {
			do_print(s, fd, "   No Members");
		} else {
			struct member *mem;
			int status;

			do_print(s, fd, "   Members: ");
			mem_iter = ao2_iterator_init(q->data->members, 0);
			while ((mem = ao2_iterator_next(&mem_iter))) {
				ao2_lock(mem);
				ast_str_set(&out, 0, "      %s", mem->membername);
				if (strcasecmp(mem->membername, mem->interface)) {
					ast_str_append(&out, 0, " (%s", mem->interface);
					ast_str_append(&out, 0, " from %s", mem->device->state_interface);
					ast_str_append(&out, 0, ")");
				}
				if (mem->penalty) {
					ast_str_append(&out, 0, " with penalty %d", mem->penalty);
				}
				status = get_device_status(mem);
				ast_str_append(&out, 0, "%s%s%s (%s)",
					mem->dynamic ? " (dynamic)" : "",
					mem->realtime ? " (realtime)" : "",
					mem->paused ? " (paused)" : "",
					ast_devstate2str(status));

				if (mem->calls) {
					ast_str_append(&out, 0, " has taken %d calls (last was %ld secs ago)",
						mem->calls, (long)ast_tvdiff_sec(ast_tvnow(), mem->lastcall));
				} else {
					ast_str_append(&out, 0, " has taken no calls yet");
				}
				do_print(s, fd, ast_str_buffer(out));
				ao2_unlock(mem);
				ao2_ref(mem, -1);
			}
			ao2_iterator_destroy(&mem_iter);
		}
		if (!q->data->count) {
			do_print(s, fd, "   No Callers");
		} else {
			struct queue_ent *qe;
			int pos = 1;

			do_print(s, fd, "   Callers: ");
			AST_LIST_LOCK(q->data->head);
			AST_LIST_TRAVERSE(q->data->head, qe, next) {
				ast_str_set(&out, 0, "      %d. %s (wait: %ld:%2.2ld, prio: %d)",
					pos++, qe->chan->name, (long)(ast_tvdiff_sec(now, qe->start)) / 60,
					(long)(ast_tvdiff_sec(now, qe->start)) % 60, qe->prio);
				do_print(s, fd, ast_str_buffer(out));
			}
			AST_LIST_UNLOCK(q->data->head);
		}
		do_print(s, fd, "");	/* blank line between entries */
		ao2_t_ref(q, -1, "Done with iterator"); /* Unref the iterator's reference */
	}
	ao2_iterator_destroy(&queue_iter);

	if (!found) {
		if (argc == 3) {
			ast_str_set(&out, 0, "No such queue: %s.", argv[2]);
		} else {
			ast_str_set(&out, 0, "No queues.");
		}
		do_print(s, fd, ast_str_buffer(out));
	}
	return CLI_SUCCESS;
}

static char *complete_queue(const char *line, const char *word, int pos, int state)
{
	struct call_queue *q;
	char *ret = NULL;
	int which = 0;
	int wordlen = strlen(word);
	struct ao2_iterator queue_iter;

	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate through queues"))) {
		if (!strncasecmp(word, q->name, wordlen) && ++which > state) {
			ret = ast_strdup(q->name);
			ao2_t_ref(q, -1, "Done with iterator");
			break;
		}
		ao2_t_ref(q, -1, "Done with iterator");
	}
	ao2_iterator_destroy(&queue_iter);

	return ret;
}

static char *complete_queue_show(const char *line, const char *word, int pos, int state)
{
	if (pos == 2)
		return complete_queue(line, word, pos, state);
	return NULL;
}

static char *queue_show(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	switch ( cmd ) {
	case CLI_INIT:
		e->command = "queue show";
		e->usage =
			"Usage: queue show\n"
			"       Provides summary information on a specified queue.\n";
		return NULL;
	case CLI_GENERATE:
		return complete_queue_show(a->line, a->word, a->pos, a->n);	
	}

	return __queues_show(NULL, a->fd, a->argc, a->argv);
}

/*!\brief callback to display queues status in manager
   \addtogroup Group_AMI
 */
static int manager_queues_show(struct mansession *s, const struct message *m)
{
	static const char * const a[] = { "queue", "show" };

	__queues_show(s, -1, 2, a);
	astman_append(s, "\r\n\r\n");	/* Properly terminate Manager output */

	return RESULT_SUCCESS;
}

static int manager_queue_rule_show(struct mansession *s, const struct message *m)
{
	const char *rule = astman_get_header(m, "Rule");
	const char *id = astman_get_header(m, "ActionID");
	struct rule_list *rl_iter;
	struct penalty_rule *pr_iter;
	struct ao2_iterator riter, piter;

	astman_append(s, "Response: Success\r\n");
	if (!ast_strlen_zero(id)) {
		astman_append(s, "ActionID: %s\r\n", id);
	}

	if (!ast_strlen_zero(rule) && (rl_iter = ao2_find(rules, (char *)rule, 0))) {
		astman_append(s, "RuleList: %s\r\n", rl_iter->name);
		piter = ao2_iterator_init(rl_iter->rules, 0);
		while ((pr_iter = ao2_iterator_next(&piter))) {
			astman_append(s, "Rule: %d,%s%d,%s%d\r\n", pr_iter->time, pr_iter->max_relative && pr_iter->max_value >= 0 ? "+" : "", pr_iter->max_value, pr_iter->min_relative && pr_iter->min_value >= 0 ? "+" : "", pr_iter->min_value );
			ao2_ref(pr_iter, -1);
		}
		ao2_iterator_destroy(&piter);
		ao2_ref(rl_iter, -1);
	} else if (ast_strlen_zero(rule)) {
		riter = ao2_iterator_init(rules, 0);
		while ((rl_iter = ao2_iterator_next(&riter))) {
			astman_append(s, "RuleList: %s\r\n", rl_iter->name);
			piter = ao2_iterator_init(rl_iter->rules, 0);
			while ((pr_iter = ao2_iterator_next(&piter))) {
				astman_append(s, "Rule: %d,%s%d,%s%d\r\n", pr_iter->time, pr_iter->max_relative && pr_iter->max_value >= 0 ? "+" : "", pr_iter->max_value, pr_iter->min_relative && pr_iter->min_value >= 0 ? "+" : "", pr_iter->min_value );
				ao2_ref(pr_iter, -1);
			}
			ao2_iterator_destroy(&piter);
		}
		ao2_iterator_destroy(&riter);
	}

	/*
	 * Two blank lines instead of one because the Response and
	 * ActionID headers used to not be present.
	 */
	astman_append(s, "\r\n\r\n");

	return RESULT_SUCCESS;
}

/*! \brief Summary of queue info via the AMI */
static int manager_queues_summary(struct mansession *s, const struct message *m)
{
	int qmemcount = 0;
	int qmemavail = 0;
	int qchancount = 0;
	int qlongestholdtime = 0;
	int status;
	const char *id = astman_get_header(m, "ActionID");
	const char *queuefilter = astman_get_header(m, "Queue");
	char idText[256] = "";
	struct call_queue *q;
	struct queue_ent *qe;
	struct member *mem;
	struct ao2_iterator queue_iter;
	struct ao2_iterator mem_iter;

	/* load realtime queue[s] */
	if (ast_strlen_zero(queuefilter)) {
		load_all_realtime_queues(NULL);
	} else if ((q = load_realtime_queue(queuefilter, NULL))) {
		ao2_ref(q, -1);
	}

	astman_send_ack(s, m, "Queue summary will follow");

	if (!ast_strlen_zero(id))
		snprintf(idText, 256, "ActionID: %s\r\n", id);
	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate through queues"))) {
		/* List queue properties */
		if (!ast_strlen_zero(queuefilter) && strcmp(q->name, queuefilter)) {
			continue;
		}
		/* Reset the necessary local variables if no queuefilter is set*/
		qmemcount = 0;
		qmemavail = 0;
		qchancount = 0;
		qlongestholdtime = 0;

		/* List Queue Members */
		mem_iter = ao2_iterator_init(q->data->members, 0);
		while ((mem = ao2_iterator_next(&mem_iter))) {
			ao2_lock(mem);
			status = get_device_status(mem);
			if ((status != AST_DEVICE_UNAVAILABLE) && (status != AST_DEVICE_INVALID)) {
				++qmemcount;
				if (((status == AST_DEVICE_NOT_INUSE) || (status == AST_DEVICE_UNKNOWN)) &&
				    !mem->paused) {
					++qmemavail;
				}
			}
			ao2_unlock(mem);
			ao2_ref(mem, -1);
		}
		ao2_iterator_destroy(&mem_iter);

		AST_LIST_LOCK(q->data->head);
		AST_LIST_TRAVERSE(q->data->head, qe, next) {
			if (ast_tvdiff_sec(ast_tvnow(), qe->start) > qlongestholdtime) {
				qlongestholdtime = ast_tvdiff_sec(ast_tvnow(), qe->start);
			}
			++qchancount;
		}
		AST_LIST_UNLOCK(q->data->head);
		ao2_lock(q->data);
		astman_append(s, "Event: QueueSummary\r\n"
			"Queue: %s\r\n"
			"LoggedIn: %d\r\n"
			"Available: %d\r\n"
			"Callers: %d\r\n"
			"HoldTime: %d\r\n"
			"TalkTime: %d\r\n"
			"LongestHoldTime: %d\r\n"
			"%s"
			"\r\n",
			q->name, qmemcount, qmemavail, qchancount, q->data->holdtime, q->data->talktime, qlongestholdtime, idText);
		ao2_unlock(q->data);
		ao2_t_ref(q, -1, "Done with iterator");
	}
	ao2_iterator_destroy(&queue_iter);
	astman_append(s,
		"Event: QueueSummaryComplete\r\n"
		"%s"
		"\r\n", idText);

	return RESULT_SUCCESS;
}

/*! \brief Queue status info via AMI */
static int manager_queues_status(struct mansession *s, const struct message *m)
{
	int pos;
	const char *id = astman_get_header(m,"ActionID");
	const char *queuefilter = astman_get_header(m,"Queue");
	const char *memberfilter = astman_get_header(m,"Member");
	char idText[256] = "";
	struct call_queue *q;
	struct queue_ent *qe;
	float sl = 0;
	int status;
	struct member *mem;
	struct ao2_iterator queue_iter;
	struct ao2_iterator mem_iter;

	astman_send_ack(s, m, "Queue status will follow");
	if (!ast_strlen_zero(id))
		snprintf(idText, sizeof(idText), "ActionID: %s\r\n", id);

	/* load realtime queue[s] */
	if (ast_strlen_zero(queuefilter)) {
		load_all_realtime_queues(NULL);
	} else if ((q = load_realtime_queue(queuefilter, NULL))) {
		ao2_ref(q, -1);
	}

	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate through queues"))) {
		/* List queue properties */
		if (!ast_strlen_zero(queuefilter) && strcmp(q->name, queuefilter)) {
			continue;
		}
		ao2_lock(q->data);
		sl = ((q->data->callscompleted > 0) ? 100 * ((float)q->data->callscompletedinsl / (float)q->data->callscompleted) : 0);
		astman_append(s, "Event: QueueParams\r\n"
			"Queue: %s\r\n"
			"Max: %d\r\n"
			"Strategy: %s\r\n"
			"Calls: %d\r\n"
			"Holdtime: %d\r\n"
			"TalkTime: %d\r\n"
			"Completed: %d\r\n"
			"Abandoned: %d\r\n"
			"ServiceLevel: %d\r\n"
			"ServicelevelPerf: %2.1f\r\n"
			"Weight: %d\r\n"
			"%s"
			"\r\n",
			q->name, q->maxlen, int2strat(q->strategy), q->data->count, q->data->holdtime, q->data->talktime,
			q->data->callscompleted, q->data->callsabandoned, q->servicelevel, sl, q->weight, idText);
		/* List Queue Members */
		ao2_unlock(q->data);
		mem_iter = ao2_iterator_init(q->data->members, 0);
		while ((mem = ao2_iterator_next(&mem_iter))) {
			ao2_lock(mem);
			if (ast_strlen_zero(memberfilter) || !strcmp(mem->interface, memberfilter) || !strcmp(mem->membername, memberfilter)) {
				status = get_device_status(mem);
				astman_append(s, "Event: QueueMember\r\n"
					"Queue: %s\r\n"
					"Name: %s\r\n"
					"Location: %s\r\n"
					"StateInterface: %s\r\n"
					"Membership: %s\r\n"
					"Penalty: %d\r\n"
					"CallsTaken: %d\r\n"
					"LastCall: %d\r\n"
					"Status: %d\r\n"
					"Paused: %d\r\n"
					"%s"
					"\r\n",
					q->name, mem->membername, mem->interface, mem->device->state_interface,
					mem->dynamic ? "dynamic" : mem->realtime ? "realtime" : "static",
					mem->penalty, mem->calls, (int)mem->lastcall.tv_sec, status, mem->paused, idText);
			}
			ao2_unlock(mem);
			ao2_ref(mem, -1);
		}
		ao2_iterator_destroy(&mem_iter);
		/* List Queue Entries */
		pos = 1;
		AST_LIST_LOCK(q->data->head);
		AST_LIST_TRAVERSE(q->data->head, qe, next) {
			astman_append(s, "Event: QueueEntry\r\n"
				"Queue: %s\r\n"
				"Position: %d\r\n"
				"Channel: %s\r\n"
				"Uniqueid: %s\r\n"
				"CallerIDNum: %s\r\n"
				"CallerIDName: %s\r\n"
				"ConnectedLineNum: %s\r\n"
				"ConnectedLineName: %s\r\n"
				"Wait: %ld\r\n"
				"%s"
				"\r\n",
				q->name, pos++, qe->chan->name, qe->chan->uniqueid,
				S_COR(qe->chan->caller.id.number.valid, qe->chan->caller.id.number.str, "unknown"),
				S_COR(qe->chan->caller.id.name.valid, qe->chan->caller.id.name.str, "unknown"),
				S_COR(qe->chan->connected.id.number.valid, qe->chan->connected.id.number.str, "unknown"),
				S_COR(qe->chan->connected.id.name.valid, qe->chan->connected.id.name.str, "unknown"),
				(long)ast_tvdiff_sec(ast_tvnow(), qe->start), idText);
		}
		AST_LIST_UNLOCK(q->data->head);
		ao2_t_ref(q, -1, "Done with iterator");
	}
	ao2_iterator_destroy(&queue_iter);

	astman_append(s,
		"Event: QueueStatusComplete\r\n"
		"%s"
		"\r\n",idText);

	return RESULT_SUCCESS;
}

static int manager_add_queue_member(struct mansession *s, const struct message *m)
{
	const char *queuename, *interface;
	struct call_queue *q;
	struct ast_config *mcfg;
	struct ast_category *mcat;

	queuename = astman_get_header(m, "Queue");
	interface = astman_get_header(m, "Interface");

	if (ast_strlen_zero(queuename)) {
		astman_send_error(s, m, "'Queue' not specified.");
		return 0;
	}

	if (ast_strlen_zero(interface)) {
		astman_send_error(s, m, "'Interface' not specified.");
		return 0;
	}

        mcfg = ast_config_new();
        mcat = ast_category_new(interface, "AMIADD", -1);

        if (!mcfg || !mcat) {
		astman_send_error(s, m, "Out of memory");
		return 0;
	} else {
		ast_category_append(mcfg, mcat);
	}

	if (!(q = load_realtime_queue(queuename, NULL))) {
		astman_send_error(s, m, "Unable to add interface to queue: No such queue");
		return 0;
	}

	add_var_to_cat(mcat, "penalty", astman_get_header(m, "Penalty"));
	add_var_to_cat(mcat, "paused", astman_get_header(m, "Paused"));
	add_var_to_cat(mcat, "membername", astman_get_header(m, "MemberName"));
	add_var_to_cat(mcat, "state_interface", astman_get_header(m, "StateInterface"));
	add_var_to_cat(mcat, "callinuse", astman_get_header(m, "CallInuse"));

	switch (handle_member_record(q, interface, mcfg, QUEUE_ADD_MEMBER_DYNAMIC, "MANAGER")) {
	case RES_OKAY:
		astman_send_ack(s, m, "Added interface to queue");
		/* write out to db */
		if (queue_persistent_members) {
			dump_queue_members(q);
		}
		break;
	case RES_ERROR:
		astman_send_ack(s, m, "Error Adding interface to queue");
		break;
	case RES_EXISTS:
		astman_send_error(s, m, "Unable to add interface: Already there");
		break;
	case RES_OUTOFMEMORY:
		astman_send_error(s, m, "Out of memory");
		break;
	}
	ast_config_destroy(mcfg);

	ao2_ref(q, -1);
	return 0;
}

static int manager_remove_queue_member(struct mansession *s, const struct message *m)
{
	const char *queuename, *interface;

	queuename = astman_get_header(m, "Queue");
	interface = astman_get_header(m, "Interface");

	if (ast_strlen_zero(queuename) || ast_strlen_zero(interface)) {
		astman_send_error(s, m, "Need 'Queue' and 'Interface' parameters.");
		return 0;
	}

	switch (remove_from_queue(queuename, interface, "MANAGER")) {
	case RES_OKAY:
		astman_send_ack(s, m, "Removed interface from queue");
		break;
	case RES_EXISTS:
		astman_send_error(s, m, "Unable to remove interface: Not there");
		break;
	case RES_NOSUCHQUEUE:
		astman_send_error(s, m, "Unable to remove interface from queue: No such queue");
		break;
	case RES_OUTOFMEMORY:
		astman_send_error(s, m, "Out of memory");
		break;
	case RES_NOT_DYNAMIC:
		astman_send_error(s, m, "Member not dynamic");
		break;
	}

	return 0;
}

static int manager_set_callinuse_queue_member(struct mansession *s, const struct message *m)
{
	struct call_queue *q;
	struct member *mem;
	const char *queuename, *interface, *callinuse_s;
	int reload = 0;

	interface = astman_get_header(m, "Interface");
	callinuse_s = astman_get_header(m, "CallInuse");
	queuename = astman_get_header(m, "Queue");

	if (ast_strlen_zero(callinuse_s) || ast_strlen_zero(interface) || ast_strlen_zero(queuename)) {
		astman_send_error(s, m, "Need 'Interface' , 'Queue' and 'CallInuse' parameters.");
		return 0;
	}

	if (!(q = load_realtime_queue(queuename, NULL))) {
		astman_send_error(s, m, "Invalid 'Queue'");
		return 0;
	}
	if (!(mem = interface_exists(q, interface))) {
		astman_send_error(s, m, "Invalid 'Interface'");
		ao2_ref(q, -1);
		return 0;
	}

	ao2_lock(mem);
	mem->callinuse = abs(ast_true(callinuse_s));
	if (mem->realtime) {
		update_realtime_member_field(mem, q->name, "callinuse", callinuse_s);
	} else if (mem->dynamic) {
		reload = 1;
	}
	astman_send_ack(s, m, mem->callinuse ? "Interface CallInuse enabled" : "Interface CallInuse disabled");
	ao2_unlock(mem);
	ao2_ref(mem, -1);

	if (reload && queue_persistent_members) {
		dump_queue_members(q);
	}
	ao2_ref(q, -1);

	return 0;
}

static int manager_pause_queue_member(struct mansession *s, const struct message *m)
{
	const char *queuename, *interface, *paused_s, *reason;
	int paused;

	interface = astman_get_header(m, "Interface");
	paused_s = astman_get_header(m, "Paused");
	queuename = astman_get_header(m, "Queue");      /* Optional - if not supplied, pause the given Interface in all queues */
	reason = astman_get_header(m, "Reason");        /* Optional - Only used for logging purposes */

	if (ast_strlen_zero(interface) || ast_strlen_zero(paused_s)) {
		astman_send_error(s, m, "Need 'Interface' and 'Paused' parameters.");
		return 0;
	}

	paused = abs(ast_true(paused_s));

	if (set_member_paused(queuename, interface, reason, paused))
		astman_send_error(s, m, "Interface not found");
	else
		astman_send_ack(s, m, paused ? "Interface paused successfully" : "Interface unpaused successfully");
	return 0;
}

static int manager_queue_log_custom(struct mansession *s, const struct message *m)
{
	const char *queuename, *event, *message, *interface, *uniqueid;

	queuename = astman_get_header(m, "Queue");
	uniqueid = astman_get_header(m, "UniqueId");
	interface = astman_get_header(m, "Interface");
	event = astman_get_header(m, "Event");
	message = astman_get_header(m, "Message");

	if (ast_strlen_zero(queuename) || ast_strlen_zero(event)) {
		astman_send_error(s, m, "Need 'Queue' and 'Event' parameters.");
		return 0;
	}

	ast_queue_log(queuename, S_OR(uniqueid, "NONE"), interface, event, "%s", message);
	astman_send_ack(s, m, "Event added successfully");

	return 0;
}

static int manager_queue_reload(struct mansession *s, const struct message *m)
{
	struct ast_flags mask = {0,};
	const char *queuename = NULL;
	int header_found = 0;

	queuename = astman_get_header(m, "Queue");
	if (!strcasecmp(S_OR(astman_get_header(m, "Members"), ""), "yes")) {
		ast_set_flag(&mask, QUEUE_RELOAD_MEMBER);
		header_found = 1;
	}
	if (!strcasecmp(S_OR(astman_get_header(m, "Rules"), ""), "yes")) {
		ast_set_flag(&mask, QUEUE_RELOAD_RULES);
		header_found = 1;
	}
	if (!strcasecmp(S_OR(astman_get_header(m, "Parameters"), ""), "yes")) {
		ast_set_flag(&mask, QUEUE_RELOAD_PARAMETERS);
		header_found = 1;
	}

	if (!header_found) {
		ast_set_flag(&mask, AST_FLAGS_ALL);
	}

	if (!reload_handler(1, &mask, queuename)) {
		astman_send_ack(s, m, "Queue reloaded successfully");
	} else {
		astman_send_error(s, m, "Error encountered while reloading queue");
	}
	return 0;
}

static int manager_queue_reset(struct mansession *s, const struct message *m)
{
	const char *queuename = NULL;
	struct ast_flags mask = {QUEUE_RESET_STATS,};
	
	queuename = astman_get_header(m, "Queue");

	if (!reload_handler(1, &mask, queuename)) {
		astman_send_ack(s, m, "Queue stats reset successfully");
	} else {
		astman_send_error(s, m, "Error encountered while resetting queue stats");
	}
	return 0;
}

static char *complete_queue_add_member(const char *line, const char *word, int pos, int state)
{
	/* 0 - queue; 1 - add; 2 - member; 3 - <interface>; 4 - to; 5 - <queue>; 6 - penalty; 7 - <penalty>; 8 - as; 9 - <membername> */
	switch (pos) {
	case 3: /* Don't attempt to complete name of interface (infinite possibilities) */
		return NULL;
	case 4: /* only one possible match, "to" */
		return state == 0 ? ast_strdup("to") : NULL;
	case 5: /* <queue> */
		return complete_queue(line, word, pos, state);
	case 6: /* only one possible match, "penalty" */
		return state == 0 ? ast_strdup("penalty") : NULL;
	case 7:
		if (state < 100) {      /* 0-99 */
			char *num;
			if ((num = ast_malloc(3))) {
				sprintf(num, "%d", state);
			}
			return num;
		} else {
			return NULL;
		}
	case 8: /* only one possible match, "as" */
		return state == 0 ? ast_strdup("as") : NULL;
	case 9: /* Don't attempt to complete name of member (infinite possibilities) */
		return NULL;
	case 10:
		return state == 0 ? ast_strdup("state_interface") : NULL;
	case 11: /* Don't attempt to complete name of state_interface (infinite possibilities) */
		return NULL;
	case 12:
		return state == 0 ? ast_strdup("callinuse") : NULL;
	case 13:
		if (!strlen(word)) {
			return  NULL;
		} else if ((state == 0) && !strncmp("yes", word, strlen(word))) {
			return ast_strdup("yes");
		} else if ((state == 0) && !strncmp("no", word, strlen(word))) {
			return ast_strdup("no");
		} else {
			return NULL;
		}
	default:
		return NULL;
	}
}

static int manager_queue_member_penalty(struct mansession *s, const struct message *m)
{
	const char *queuename, *interface, *penalty_s;
	int penalty;

	interface = astman_get_header(m, "Interface");
	penalty_s = astman_get_header(m, "Penalty");
	/* Optional - if not supplied, set the penalty value for the given Interface in all queues */
	queuename = astman_get_header(m, "Queue");

	if (ast_strlen_zero(interface) || ast_strlen_zero(penalty_s)) {
		astman_send_error(s, m, "Need 'Interface' and 'Penalty' parameters.");
		return 0;
	}
 
	penalty = atoi(penalty_s);

	if (set_member_penalty((char *)queuename, (char *)interface, penalty))
		astman_send_error(s, m, "Invalid interface, queuename or penalty");
	else
		astman_send_ack(s, m, "Interface penalty set successfully");

	return 0;
}

static char *handle_queue_add_member(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	struct call_queue *q;
	int res = 0;
	struct ast_config *mcfg;
	struct ast_category *mcat;

	switch ( cmd ) {
	case CLI_INIT:
		e->command = "queue add member";
		e->usage =
			"Usage: queue add member <channel> to <queue> [[[[penalty <penalty>] as <membername>] state_interface <interface>] callinuse {yes|no}]\n"
			"       Add a channel to a queue with optionally:  a penalty, membername, callinuse and a state_interface\n";
		return NULL;
	case CLI_GENERATE:
		return complete_queue_add_member(a->line, a->word, a->pos, a->n);
	}

	if ((a->argc != 6) && (a->argc != 8) && (a->argc != 10) && (a->argc != 12) && (a->argc != 14)) {
		return CLI_SHOWUSAGE;
	} else if (strcmp(a->argv[4], "to")) {
		return CLI_SHOWUSAGE;
	} else if ((a->argc >= 8) && strcmp(a->argv[6], "penalty")) {
		return CLI_SHOWUSAGE;
	} else if ((a->argc >= 10) && strcmp(a->argv[8], "as")) {
		return CLI_SHOWUSAGE;
	} else if ((a->argc == 12) && strcmp(a->argv[10], "state_interface")) {
		return CLI_SHOWUSAGE;
	} else if ((a->argc == 14) && strcmp(a->argv[12], "callinuse")) {
		return CLI_SHOWUSAGE;
	}

	mcfg = ast_config_new();
	mcat = ast_category_new(a->argv[3], "queue_add_member_cli", -1);

	if (!mcfg || !mcat) {
		ast_cli(a->fd, "Out of memory\n");
		return CLI_FAILURE;
	} else {
		ast_category_append(mcfg, mcat);
	}

	if (!(q = load_realtime_queue(a->argv[5], NULL))) {
		ast_cli(a->fd, "Unable to add interface to queue '%s': No such queue\n", a->argv[5]);
		return CLI_FAILURE;
	}

	add_var_to_cat(mcat, "penalty", a->argv[7]);
	add_var_to_cat(mcat, "membername", a->argv[9]);
	add_var_to_cat(mcat, "state_interface", a->argv[11]);
	add_var_to_cat(mcat, "callinuse", a->argv[13]);

	res = handle_member_record(q, a->argv[3], mcfg, QUEUE_ADD_MEMBER_DYNAMIC, "CLI");

	ast_config_destroy(mcfg);

	/* write out to db */
	if ((res == RES_OKAY) && queue_persistent_members) {
		dump_queue_members(q);
	}
	ao2_ref(q, -1);

	switch (res) {
	case RES_OKAY:
		ast_cli(a->fd, "Added interface '%s' to queue '%s'\n", a->argv[3], a->argv[5]);
		return CLI_SUCCESS;
	case RES_EXISTS:
		ast_cli(a->fd, "Unable to add interface '%s' to queue '%s': Already there\n", a->argv[3], a->argv[5]);
		return CLI_FAILURE;
	case RES_OUTOFMEMORY:
		ast_cli(a->fd, "Out of memory\n");
		return CLI_FAILURE;
	case RES_ERROR:
		ast_cli(a->fd, "Error adding interface %s to queue '%s': incorrect paramaters\n", a->argv[3], a->argv[5]);
		return CLI_FAILURE;
	case RES_NOT_DYNAMIC:
		ast_cli(a->fd, "Member not dynamic\n");
		return CLI_FAILURE;
	default:
		return CLI_FAILURE;
	}
}

static char *complete_queue_remove_member(const char *line, const char *word, int pos, int state)
{
	int which = 0;
	struct call_queue *q;
	struct member *m;
	struct ao2_iterator queue_iter;
	struct ao2_iterator mem_iter;
	int wordlen = strlen(word);
	char *tmp;

	/* 0 - queue; 1 - remove; 2 - member; 3 - <member>; 4 - from; 5 - <queue> */
	if (pos > 5 || pos < 3)
		return NULL;
	if (pos == 4)   /* only one possible match, 'from' */
		return (state == 0 ? ast_strdup("from") : NULL);

	if (pos == 5)   /* No need to duplicate code */
		return complete_queue(line, word, pos, state);

	/* here is the case for 3, <member> */
	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_t_iterator_next(&queue_iter, "Iterate through queues"))) {
		mem_iter = ao2_iterator_init(q->data->members, 0);
		while ((m = ao2_iterator_next(&mem_iter))) {
			ao2_lock(m);
			if (!strncasecmp(word, m->membername, wordlen) && ++which > state) {
				tmp = ast_strdup(m->interface);
				ao2_ref(m, -1);
				ao2_unlock(m);
				ao2_t_ref(q, -1, "Done with iterator, returning interface name");
				ao2_iterator_destroy(&mem_iter);
				ao2_iterator_destroy(&queue_iter);
				return tmp;
			}
			ao2_unlock(m);
			ao2_ref(m, -1);
		}
		ao2_iterator_destroy(&mem_iter);
		ao2_t_ref(q, -1, "Done with iterator");
	}
	ao2_iterator_destroy(&queue_iter);

	return NULL;
}

static char *handle_queue_remove_member(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	const char *queuename, *interface;

	switch (cmd) {
	case CLI_INIT:
		e->command = "queue remove member";
		e->usage =
			"Usage: queue remove member <channel> from <queue>\n"
			"       Remove a specific channel from a queue.\n";
		return NULL;
	case CLI_GENERATE:
		return complete_queue_remove_member(a->line, a->word, a->pos, a->n);
	}

	if (a->argc != 6) {
		return CLI_SHOWUSAGE;
	} else if (strcmp(a->argv[4], "from")) {
		return CLI_SHOWUSAGE;
	}

	queuename = a->argv[5];
	interface = a->argv[3];

	switch (remove_from_queue(queuename, interface, "CLI")) {
	case RES_OKAY:
		ast_cli(a->fd, "Removed interface %s from queue '%s'\n", interface, queuename);
		return CLI_SUCCESS;
	case RES_EXISTS:
		ast_cli(a->fd, "Unable to remove interface '%s' from queue '%s': Not there\n", interface, queuename);
		return CLI_FAILURE;
	case RES_NOSUCHQUEUE:
		ast_cli(a->fd, "Unable to remove interface from queue '%s': No such queue\n", queuename);
		return CLI_FAILURE;
	case RES_OUTOFMEMORY:
		ast_cli(a->fd, "Out of memory\n");
		return CLI_FAILURE;
	case RES_NOT_DYNAMIC:
		ast_cli(a->fd, "Unable to remove interface '%s' from queue '%s': Member is not dynamic\n", interface, queuename);
		return CLI_FAILURE;
	default:
		return CLI_FAILURE;
	}
}

static char *complete_queue_pause_member(const char *line, const char *word, int pos, int state)
{
	/* 0 - queue; 1 - pause; 2 - member; 3 - <interface>; 4 - queue; 5 - <queue>; 6 - reason; 7 - <reason> */
	switch (pos) {
	case 3:	/* Don't attempt to complete name of interface (infinite possibilities) */
		return NULL;
	case 4:	/* only one possible match, "queue" */
		return state == 0 ? ast_strdup("queue") : NULL;
	case 5:	/* <queue> */
		return complete_queue(line, word, pos, state);
	case 6: /* "reason" */
		return state == 0 ? ast_strdup("reason") : NULL;
	case 7: /* Can't autocomplete a reason, since it's 100% customizeable */
		return NULL;
	default:
		return NULL;
	}
}

static char *handle_queue_pause_member(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	const char *queuename, *interface, *reason;
	int paused;

	switch (cmd) {
	case CLI_INIT:
		e->command = "queue {pause|unpause} member";
		e->usage = 
			"Usage: queue {pause|unpause} member <member> [queue <queue> [reason <reason>]]\n"
			"	Pause or unpause a queue member. Not specifying a particular queue\n"
			"	will pause or unpause a member across all queues to which the member\n"
			"	belongs.\n";
		return NULL;
	case CLI_GENERATE:
		return complete_queue_pause_member(a->line, a-> word, a->pos, a->n);
	}

	if (a->argc < 4 || a->argc == 5 || a->argc == 7 || a->argc > 8) {
		return CLI_SHOWUSAGE;
	} else if (a->argc >= 5 && strcmp(a->argv[4], "queue")) {
		return CLI_SHOWUSAGE;
	} else if (a->argc == 8 && strcmp(a->argv[6], "reason")) {
		return CLI_SHOWUSAGE;
	}


	interface = a->argv[3];
	queuename = a->argc >= 6 ? a->argv[5] : NULL;
	reason = a->argc == 8 ? a->argv[7] : NULL;
	paused = !strcasecmp(a->argv[1], "pause");

	if (set_member_paused(queuename, interface, reason, paused) == RESULT_SUCCESS) {
		ast_cli(a->fd, "%spaused interface '%s'", paused ? "" : "un", interface);
		if (!ast_strlen_zero(queuename))
			ast_cli(a->fd, " in queue '%s'", queuename);
		if (!ast_strlen_zero(reason))
			ast_cli(a->fd, " for reason '%s'", reason);
		ast_cli(a->fd, "\n");
		return CLI_SUCCESS;
	} else {
		ast_cli(a->fd, "Unable to %spause interface '%s'", paused ? "" : "un", interface);
		if (!ast_strlen_zero(queuename))
			ast_cli(a->fd, " in queue '%s'", queuename);
		if (!ast_strlen_zero(reason))
			ast_cli(a->fd, " for reason '%s'", reason);
		ast_cli(a->fd, "\n");
		return CLI_FAILURE;
	}
}

static char *complete_queue_callinuse_member(const char *line, const char *word, int pos, int state)
{
	/* 0 - queue; 1 - set; 2 - callinuse; 3 - {yes|no}; 4 - for; 5 - <member>; 6 - in; 7 - <queue>;*/
	switch (pos) {
	case 4:
		if (state == 0) {
			return ast_strdup("for");
		} else {
			return NULL;
		}
	case 6:
		if (state == 0) {
			return ast_strdup("in");
		} else {
			return NULL;
		}
	case 7:
		return complete_queue(line, word, pos, state);
	default:
		return NULL;
	}
}

static char *handle_queue_callinuse_member(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	struct call_queue *q;
	struct member *m;
	int reload = 0;

	switch (cmd) {
	case CLI_INIT:
		e->command = "queue set callinuse {yes|no}";
		e->usage =
			"Usage: queue set callinuse { yes | no } for <member> in <queue>\n"
			"	Set or unset callinuse status of a queue member.\n";
		return NULL;
	case CLI_GENERATE:
		return complete_queue_callinuse_member(a->line, a->word, a->pos, a->n);
	}

	if (a->argc != 8) {
		return CLI_SHOWUSAGE;
	} else if (strcmp(a->argv[4], "for")) {
		return CLI_SHOWUSAGE;
	} else if (strcmp(a->argv[6], "in")) {
		return CLI_SHOWUSAGE;
	}

	if (!(q = load_realtime_queue(a->argv[7], NULL))) {
		return CLI_FAILURE;
	}
	if ((m = interface_exists(q, a->argv[5]))) {
		ao2_lock(m);
		m->callinuse = abs(ast_true(a->argv[3]));
		if (m->realtime) {
			update_realtime_member_field(m, q->name, "callinuse", a->argv[3]);
		} else if (m->dynamic) {
			reload = 1;
		}
		ao2_unlock(m);
		ao2_ref(m, -1);

		if (reload && queue_persistent_members) {
			dump_queue_members(q);
		}
		ao2_ref(q, -1);
		return CLI_SUCCESS;
	} else {
		ao2_ref(q, -1);
		return CLI_FAILURE;
	}
}

static char *complete_queue_set_member_penalty(const char *line, const char *word, int pos, int state)
{
	/* 0 - queue; 1 - set; 2 - penalty; 3 - <penalty>; 4 - on; 5 - <member>; 6 - in; 7 - <queue>;*/
	switch (pos) {
	case 4:
		if (state == 0) {
			return ast_strdup("on");
		} else {
			return NULL;
		}
	case 6:
		if (state == 0) {
			return ast_strdup("in");
		} else {
			return NULL;
		}
	case 7:
		return complete_queue(line, word, pos, state);
	default:
		return NULL;
	}
}
 
static char *handle_queue_set_member_penalty(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	const char *queuename = NULL, *interface;
	int penalty = 0;

	switch (cmd) {
	case CLI_INIT:
		e->command = "queue set penalty";
		e->usage = 
		"Usage: queue set penalty <penalty> on <interface> [in <queue>]\n"
		"	Set a member's penalty in the queue specified. If no queue is specified\n"
		"	then that interface's penalty is set in all queues to which that interface is a member\n";
		return NULL;
	case CLI_GENERATE:
		return complete_queue_set_member_penalty(a->line, a->word, a->pos, a->n);
	}

	if (a->argc != 6 && a->argc != 8) {
		return CLI_SHOWUSAGE;
	} else if (strcmp(a->argv[4], "on") || (a->argc > 6 && strcmp(a->argv[6], "in"))) {
		return CLI_SHOWUSAGE;
	}

	if (a->argc == 8)
		queuename = a->argv[7];
	interface = a->argv[5];
	penalty = atoi(a->argv[3]);

	switch (set_member_penalty(queuename, interface, penalty)) {
	case RESULT_SUCCESS:
		ast_cli(a->fd, "Set penalty on interface '%s' from queue '%s'\n", interface, queuename);
		return CLI_SUCCESS;
	case RESULT_FAILURE:
		ast_cli(a->fd, "Failed to set penalty on interface '%s' from queue '%s'\n", interface, queuename);
		return CLI_FAILURE;
	default:
		return CLI_FAILURE;
	}
}

static char *complete_queue_rule_show(const char *line, const char *word, int pos, int state) 
{
	int which = 0;
	struct rule_list *rl_iter;
	int wordlen = strlen(word);
	char *ret = NULL;
	struct ao2_iterator riter;

	if (pos != 3) /* Wha? */ {
		return NULL;
	}

	riter = ao2_iterator_init(rules, 0);
	while ((rl_iter = ao2_iterator_next(&riter))) {
		if (!strncasecmp(word, rl_iter->name, wordlen) && ++which > state) {
			ret = ast_strdup(rl_iter->name);
			break;
		}
	}
	ao2_iterator_destroy(&riter);

	return ret;
}

static char *handle_queue_rule_show(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	const char *rule;
	struct rule_list *rl_iter;
	struct penalty_rule *pr_iter;
	struct ao2_iterator riter, piter;

	switch (cmd) {
	case CLI_INIT:
		e->command = "queue show rules";
		e->usage =
		"Usage: queue show rules [rulename]\n"
		"	Show the list of rules associated with rulename. If no\n"
		"	rulename is specified, list all rules defined in queuerules.conf\n";
		return NULL;
	case CLI_GENERATE:
		return complete_queue_rule_show(a->line, a->word, a->pos, a->n);
	}

	if (a->argc != 3 && a->argc != 4)
		return CLI_SHOWUSAGE;

	rule = a->argc == 4 ? a->argv[3] : "";

	riter = ao2_iterator_init(rules, 0);
	while ((rl_iter = ao2_iterator_next(&riter))) {
		if (ast_strlen_zero(rule) || !strcasecmp(rl_iter->name, rule)) {
			ast_cli(a->fd, "Rule: %s\n", rl_iter->name);
			piter = ao2_iterator_init(rl_iter->rules, 0);
			while ((pr_iter = ao2_iterator_next(&piter))) {
				ast_cli(a->fd, "\tAfter %d seconds, adjust QUEUE_MAX_PENALTY %s %d and adjust QUEUE_MIN_PENALTY %s %d\n", pr_iter->time, pr_iter->max_relative ? "by" : "to", pr_iter->max_value, pr_iter->min_relative ? "by" : "to", pr_iter->min_value);
				ao2_ref(pr_iter, -1);
			}
			ao2_iterator_destroy(&piter);
		}
	}
	ao2_iterator_destroy(&riter);

	return CLI_SUCCESS;
}

static char *handle_queue_reset(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	struct ast_flags mask = {QUEUE_RESET_STATS,};
	int i;

	switch (cmd) {
		case CLI_INIT:
			e->command = "queue reset stats";
			e->usage =
				"Usage: queue reset stats [<queuenames>]\n"
				"\n"
				"Issuing this command will reset statistics for\n"
				"<queuenames>, or for all queues if no queue is\n"
				"specified.\n";
			return NULL;
		case CLI_GENERATE:
			if (a->pos >= 3) {
				return complete_queue(a->line, a->word, a->pos, a->n);
			} else {
				return NULL;
			}
	}

	if (a->argc < 3) {
		return CLI_SHOWUSAGE;
	}

	if (a->argc == 3) {
		reload_handler(1, &mask, NULL);
		return CLI_SUCCESS;
	}

	for (i = 3; i < a->argc; ++i) {
		reload_handler(1, &mask, a->argv[i]);
	}

	return CLI_SUCCESS;
}

static char *handle_queue_reload(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	struct ast_flags mask = {0,};
	int i;

	switch (cmd) {
		case CLI_INIT:
			e->command = "queue reload {parameters|members|rules|all}";
			e->usage =
				"Usage: queue reload {parameters|members|rules|all} [<queuenames>]\n"
				"Reload queues. If <queuenames> are specified, only reload information pertaining\n"
				"to <queuenames>. One of 'parameters,' 'members,' 'rules,' or 'all' must be\n"
				"specified in order to know what information to reload. Below is an explanation\n"
				"of each of these qualifiers.\n"
				"\n"
				"\t'members' - reload queue members from queues.conf\n"
				"\t'parameters' - reload all queue options except for queue members\n"
				"\t'rules' - reload the queuerules.conf file\n"
				"\t'all' - reload queue rules, parameters, and members\n"
				"\n"
				"Note: the 'rules' qualifier here cannot actually be applied to a specific queue.\n"
				"Use of the 'rules' qualifier causes queuerules.conf to be reloaded. Even if only\n"
				"one queue is specified when using this command, reloading queue rules may cause\n"
				"other queues to be affected\n";
			return NULL;
		case CLI_GENERATE:
			if (a->pos >= 3) {
				return complete_queue(a->line, a->word, a->pos, a->n);
			} else {
				return NULL;
			}
	}

	if (a->argc < 3)
		return CLI_SHOWUSAGE;

	if (!strcasecmp(a->argv[2], "rules")) {
		ast_set_flag(&mask, QUEUE_RELOAD_RULES);
	} else if (!strcasecmp(a->argv[2], "members")) {
		ast_set_flag(&mask, QUEUE_RELOAD_MEMBER);
	} else if (!strcasecmp(a->argv[2], "parameters")) {
		ast_set_flag(&mask, QUEUE_RELOAD_PARAMETERS);
	} else if (!strcasecmp(a->argv[2], "all")) {
		ast_set_flag(&mask, AST_FLAGS_ALL);
	}

	if (a->argc == 3) {
		reload_handler(1, &mask, NULL);
		return CLI_SUCCESS;
	}

	for (i = 3; i < a->argc; ++i) {
		reload_handler(1, &mask, a->argv[i]);
	}

	return CLI_SUCCESS;
}

static struct ast_cli_entry cli_queue[] = {
	AST_CLI_DEFINE(queue_show, "Show status of a specified queue"),
	AST_CLI_DEFINE(handle_queue_add_member, "Add a channel to a specified queue"),
	AST_CLI_DEFINE(handle_queue_remove_member, "Removes a channel from a specified queue"),
	AST_CLI_DEFINE(handle_queue_pause_member, "Pause or unpause a queue member"),
	AST_CLI_DEFINE(handle_queue_callinuse_member, "Set or unset callinuse queue member"),
	AST_CLI_DEFINE(handle_queue_set_member_penalty, "Set penalty for a channel of a specified queue"),
	AST_CLI_DEFINE(handle_queue_rule_show, "Show the rules defined in queuerules.conf"),
	AST_CLI_DEFINE(handle_queue_reload, "Reload queues, members, queue rules, or parameters"),
	AST_CLI_DEFINE(handle_queue_reset, "Reset statistics for a queue"),
	AST_CLI_DEFINE(queue_refshow, "Show ref stats of queue[s]"),
};

/* struct call_queue astdata mapping. */
#define DATA_EXPORT_CALL_QUEUE(MEMBER)					\
	MEMBER(call_queue, name, AST_DATA_STRING)			\
	MEMBER(call_queue, moh, AST_DATA_STRING)			\
	MEMBER(call_queue, announce, AST_DATA_STRING)			\
	MEMBER(call_queue, context, AST_DATA_STRING)			\
	MEMBER(call_queue, membermacro, AST_DATA_STRING)		\
	MEMBER(call_queue, membergosub, AST_DATA_STRING)		\
	MEMBER(call_queue, defaultrule, AST_DATA_STRING)		\
	MEMBER(call_queue, sound_next, AST_DATA_STRING)			\
	MEMBER(call_queue, sound_thereare, AST_DATA_STRING)		\
	MEMBER(call_queue, sound_calls, AST_DATA_STRING)		\
	MEMBER(call_queue, queue_quantity1, AST_DATA_STRING)		\
	MEMBER(call_queue, queue_quantity2, AST_DATA_STRING)		\
	MEMBER(call_queue, sound_holdtime, AST_DATA_STRING)		\
	MEMBER(call_queue, sound_minutes, AST_DATA_STRING)		\
	MEMBER(call_queue, sound_minute, AST_DATA_STRING)		\
	MEMBER(call_queue, sound_seconds, AST_DATA_STRING)		\
	MEMBER(call_queue, sound_thanks, AST_DATA_STRING)		\
	MEMBER(call_queue, sound_callerannounce, AST_DATA_STRING)	\
	MEMBER(call_queue, sound_reporthold, AST_DATA_STRING)		\
	MEMBER(call_queue, dead, AST_DATA_BOOLEAN)			\
	MEMBER(call_queue, eventwhencalled, AST_DATA_BOOLEAN)		\
	MEMBER(call_queue, ringinuse, AST_DATA_BOOLEAN)			\
	MEMBER(call_queue, setinterfacevar, AST_DATA_BOOLEAN)		\
	MEMBER(call_queue, setqueuevar, AST_DATA_BOOLEAN)		\
	MEMBER(call_queue, setqueueentryvar, AST_DATA_BOOLEAN)		\
	MEMBER(call_queue, reportholdtime, AST_DATA_BOOLEAN)		\
	MEMBER(call_queue, timeoutrestart, AST_DATA_BOOLEAN)		\
	MEMBER(call_queue, announceholdtime, AST_DATA_INTEGER)		\
	MEMBER(call_queue, maskmemberstatus, AST_DATA_BOOLEAN)		\
	MEMBER(call_queue, realtime, AST_DATA_BOOLEAN)			\
	MEMBER(call_queue, announcepositionlimit, AST_DATA_INTEGER)	\
	MEMBER(call_queue, announcefrequency, AST_DATA_SECONDS)		\
	MEMBER(call_queue, minannouncefrequency, AST_DATA_SECONDS)	\
	MEMBER(call_queue, periodicannouncefrequency, AST_DATA_SECONDS)	\
	MEMBER(call_queue, numperiodicannounce, AST_DATA_INTEGER)	\
	MEMBER(call_queue, randomperiodicannounce, AST_DATA_INTEGER)	\
	MEMBER(call_queue, roundingseconds, AST_DATA_SECONDS)		\
	MEMBER(call_queue, servicelevel, AST_DATA_INTEGER)		\
	MEMBER(call_queue, monfmt, AST_DATA_STRING)			\
	MEMBER(call_queue, montype, AST_DATA_INTEGER)			\
	MEMBER(call_queue, maxlen, AST_DATA_INTEGER)			\
	MEMBER(call_queue, wrapuptime, AST_DATA_SECONDS)		\
	MEMBER(call_queue, retry, AST_DATA_SECONDS)			\
	MEMBER(call_queue, timeout, AST_DATA_SECONDS)			\
	MEMBER(call_queue, weight, AST_DATA_INTEGER)			\
	MEMBER(call_queue, autopause, AST_DATA_INTEGER)			\
	MEMBER(call_queue, timeoutpriority, AST_DATA_INTEGER)		\
	MEMBER(call_queue, memberdelay, AST_DATA_INTEGER)		\
	MEMBER(call_queue, autofill, AST_DATA_INTEGER)			\

AST_DATA_STRUCTURE(call_queue, DATA_EXPORT_CALL_QUEUE);

#define DATA_EXPORT_QUEUE_DATA(MEMBER)					\
	MEMBER(queue_data, wrapped, AST_DATA_BOOLEAN)			\
	MEMBER(queue_data, holdtime, AST_DATA_SECONDS)			\
	MEMBER(queue_data, talktime, AST_DATA_SECONDS)			\
	MEMBER(queue_data, callscompleted, AST_DATA_INTEGER)		\
	MEMBER(queue_data, callsabandoned, AST_DATA_INTEGER)		\
	MEMBER(queue_data, callscompletedinsl, AST_DATA_INTEGER)	\
	MEMBER(queue_data, count, AST_DATA_INTEGER)			\
	MEMBER(queue_data, rrpos, AST_DATA_INTEGER)			\
	MEMBER(queue_data, members, AST_DATA_CONTAINER)

AST_DATA_STRUCTURE(queue_data, DATA_EXPORT_QUEUE_DATA);

/* struct member astdata mapping. */
#define DATA_EXPORT_MEMBER(MEMBER)					\
	MEMBER(member, interface, AST_DATA_STRING)			\
	MEMBER(member, membername, AST_DATA_STRING)			\
	MEMBER(member, penalty, AST_DATA_INTEGER)			\
	MEMBER(member, calls, AST_DATA_INTEGER)				\
	MEMBER(member, dynamic, AST_DATA_INTEGER)			\
	MEMBER(member, realtime, AST_DATA_INTEGER)			\
	MEMBER(member, paused, AST_DATA_INTEGER)			\
	MEMBER(member, callinuse, AST_DATA_INTEGER)			\
	MEMBER(member, rt_uniqueid, AST_DATA_STRING)

AST_DATA_STRUCTURE(member, DATA_EXPORT_MEMBER);

/* struct mem_status astdata mapping */
#define DATA_EXPORT_CALL_DEVICE(MEMBER)					\
	MEMBER(mem_state, state_interface, AST_DATA_STRING)		\
	MEMBER(mem_state, status, AST_DATA_INTEGER)			\
	MEMBER(mem_state, reserved, AST_DATA_INTEGER)			\
	MEMBER(mem_state, active, AST_DATA_INTEGER)

AST_DATA_STRUCTURE(mem_state, DATA_EXPORT_CALL_DEVICE);

#define DATA_EXPORT_QUEUE_ENT(MEMBER)						\
	MEMBER(queue_ent, digits, AST_DATA_STRING)				\
	MEMBER(queue_ent, valid_digits, AST_DATA_INTEGER)			\
	MEMBER(queue_ent, pos, AST_DATA_INTEGER)				\
	MEMBER(queue_ent, prio, AST_DATA_INTEGER)				\
	MEMBER(queue_ent, last_pos_said, AST_DATA_INTEGER)			\
	MEMBER(queue_ent, last_periodic_announce_sound, AST_DATA_INTEGER)	\
	MEMBER(queue_ent, opos, AST_DATA_INTEGER)				\
	MEMBER(queue_ent, handled, AST_DATA_INTEGER)				\
	MEMBER(queue_ent, pending, AST_DATA_INTEGER)				\
	MEMBER(queue_ent, max_penalty, AST_DATA_INTEGER)			\
	MEMBER(queue_ent, min_penalty, AST_DATA_INTEGER)			\
	MEMBER(queue_ent, linpos, AST_DATA_INTEGER)				\
	MEMBER(queue_ent, linwrapped, AST_DATA_INTEGER)				\
	MEMBER(queue_ent, cancel_answered_elsewhere, AST_DATA_INTEGER)

AST_DATA_STRUCTURE(queue_ent, DATA_EXPORT_QUEUE_ENT);

/*!
 * \internal
 * \brief Add a queue to the data_root node.
 * \param[in] search The search tree.
 * \param[in] data_root The main result node.
 * \param[in] queue The queue to add.
 */
static void queues_data_provider_get_helper(const struct ast_data_search *search,
	struct ast_data *data_root, struct call_queue *queue)
{
	struct ao2_iterator im;
	struct member *member;
	struct queue_ent *qe;
	struct ast_data *data_queue, *data_members = NULL, *enum_node;
	struct ast_data *data_member, *data_callers = NULL, *data_caller, *data_caller_channel;

	data_queue = ast_data_add_node(data_root, "queue");
	if (!data_queue) {
		return;
	}

	ast_data_add_structure(call_queue, data_queue, queue);

	ast_data_add_str(data_queue, "strategy", int2strat(queue->strategy));
	ast_data_add_int(data_queue, "membercount", ao2_container_count(queue->data->members));

	/* announce position */
	enum_node = ast_data_add_node(data_queue, "announceposition");
	if (!enum_node) {
		return;
	}
	switch (queue->announceposition) {
	case ANNOUNCEPOSITION_LIMIT:
		ast_data_add_str(enum_node, "text", "limit");
		break;
	case ANNOUNCEPOSITION_MORE_THAN:
		ast_data_add_str(enum_node, "text", "more");
		break;
	case ANNOUNCEPOSITION_YES:
		ast_data_add_str(enum_node, "text", "yes");
		break;
	case ANNOUNCEPOSITION_NO:
		ast_data_add_str(enum_node, "text", "no");
		break;
	default:
		ast_data_add_str(enum_node, "text", "unknown");
		break;
	}
	ast_data_add_int(enum_node, "value", queue->announceposition);

	/* add queue members */
	im = ao2_iterator_init(queue->data->members, 0);
	while ((member = ao2_iterator_next(&im))) {
		if (!data_members) {
			data_members = ast_data_add_node(data_queue, "members");
			if (!data_members) {
				ao2_ref(member, -1);
				continue;
			}
		}

		data_member = ast_data_add_node(data_members, "member");
		if (!data_member) {
			ao2_ref(member, -1);
			continue;
		}

		ao2_lock(member);
		ast_data_add_structure(member, data_member, member);
		ao2_unlock(member);
		ao2_ref(member, -1);
	}

	/* include the callers inside the result. */
	AST_LIST_LOCK(queue->data->head);
	AST_LIST_TRAVERSE(queue->data->head, qe, next) {
		if (!data_callers) {
			data_callers = ast_data_add_node(data_queue, "callers");
			if (!data_callers) {
				continue;
			}
		}

		data_caller = ast_data_add_node(data_callers, "caller");
		if (!data_caller) {
			continue;
		}

		ast_data_add_structure(queue_ent, data_caller, qe);

		/* add the caller channel. */
		data_caller_channel = ast_data_add_node(data_caller, "channel");
		if (!data_caller_channel) {
			continue;
		}

		ast_channel_data_add_structure(data_caller_channel, qe->chan, 1);
	}
	AST_LIST_UNLOCK(queue->data->head);

	/* if this queue doesn't match remove the added queue. */
	if (!ast_data_search_match(search, data_queue)) {
		ast_data_remove_node(data_root, data_queue);
	}
}

/*!
 * \internal
 * \brief Callback used to generate the queues tree.
 * \param[in] search The search pattern tree.
 * \retval NULL on error.
 * \retval non-NULL The generated tree.
 */
static int queues_data_provider_get(const struct ast_data_search *search,
	struct ast_data *data_root)
{
	struct ao2_iterator i;
	struct call_queue *queue;

	/* load all queues from realtime*/
	load_all_realtime_queues(NULL);

	/* static queues. */
	i = ao2_iterator_init(queues, 0);
	while ((queue = ao2_iterator_next(&i))) {
		queues_data_provider_get_helper(search, data_root, queue);
		ao2_ref(queue, -1);
	}
	ao2_iterator_destroy(&i);

	return 0;
}

static const struct ast_data_handler queues_data_provider = {
	.version = AST_DATA_HANDLER_VERSION,
	.get = queues_data_provider_get
};

static const struct ast_data_entry queue_data_providers[] = {
	AST_DATA_ENTRY("asterisk/application/queue/list", &queues_data_provider),
};

static int unload_module(void)
{
	int res;
	struct ast_context *con;

	ast_cli_unregister_multiple(cli_queue, ARRAY_LEN(cli_queue));
	res = ast_manager_unregister("QueueStatus");
	res |= ast_manager_unregister("Queues");
	res |= ast_manager_unregister("QueueRule");
	res |= ast_manager_unregister("QueueSummary");
	res |= ast_manager_unregister("QueueAdd");
	res |= ast_manager_unregister("QueueRemove");
	res |= ast_manager_unregister("QueuePause");
	res |= ast_manager_unregister("QueueLog");
	res |= ast_manager_unregister("QueuePenalty");
	res |= ast_manager_unregister("QueueCallInuse");
	res |= ast_unregister_application(app_aqm);
	res |= ast_unregister_application(app_rqm);
	res |= ast_unregister_application(app_pqm);
	res |= ast_unregister_application(app_upqm);
	res |= ast_unregister_application(app_ql);
	res |= ast_unregister_application(app);
	res |= ast_custom_function_unregister(&queueexists_function);
	res |= ast_custom_function_unregister(&queuevar_function);
	res |= ast_custom_function_unregister(&queuemembercount_function);
	res |= ast_custom_function_unregister(&queuememberlist_function);
	res |= ast_custom_function_unregister(&queuewaitingcount_function);
	res |= ast_custom_function_unregister(&queuememberpenalty_function);

	res |= ast_data_unregister(NULL);

	if (device_state_sub)
		ast_event_unsubscribe(device_state_sub);

	ast_extension_state_del(0, extension_state_cb);

	if ((con = ast_context_find("app_queue_gosub_virtual_context"))) {
		ast_context_remove_extension2(con, "s", 1, NULL, 0);
		ast_context_destroy(con, "app_queue"); /* leave no trace */
	}

	ao2_callback(queues, OBJ_UNLINK | OBJ_NODATA | OBJ_MULTIPLE, remove_all_members, NULL);
	ao2_ref(queues, -1);

	ao2_callback(qdata, OBJ_UNLINK | OBJ_NODATA | OBJ_MULTIPLE, NULL, NULL);
	ao2_ref(qdata, -1);

	ao2_callback(rules, OBJ_UNLINK | OBJ_NODATA | OBJ_MULTIPLE, NULL, NULL);
	ao2_ref(rules, -1);

	ao2_callback(devices, OBJ_UNLINK | OBJ_NODATA | OBJ_MULTIPLE, NULL, NULL);
	ao2_ref(devices, -1);

	ast_unload_realtime("queue_members");
	devicestate_tps = ast_taskprocessor_unreference(devicestate_tps);
	return res;
}

static int load_module(void)
{
	int res;
	struct ast_context *con;
	struct ast_flags mask = {AST_FLAGS_ALL, };

	queues = ao2_container_alloc(MAX_QUEUE_BUCKETS, queue_hash_cb, queue_cmp_cb);
	devices = ao2_container_alloc(MAX_QUEUE_BUCKETS, device_hash_cb, device_cmp_cb);
	rules = ao2_container_alloc(MAX_QUEUE_BUCKETS, rules_hash_cb, rules_cmp_cb);
	qdata = ao2_container_alloc(MAX_QUEUE_BUCKETS, qdata_hash_cb, qdata_cmp_cb);

	use_weight = 0;

	if (reload_handler(0, &mask, NULL)) {
		return AST_MODULE_LOAD_DECLINE;
	}

	if (!(con = ast_context_find_or_create(NULL, NULL, "app_queue_gosub_virtual_context", "app_queue"))) {
		ast_log(LOG_ERROR, "Queue virtual context 'app_queue_gosub_virtual_context' does not exist and unable to create\n");
	} else {
		ast_add_extension2(con, 1, "s", 1, NULL, NULL, "NoOp", ast_strdup(""), ast_free_ptr, "app_queue");
	}

	ast_data_register_multiple(queue_data_providers, ARRAY_LEN(queue_data_providers));

	ast_cli_register_multiple(cli_queue, ARRAY_LEN(cli_queue));
	res = ast_register_application_xml(app, queue_exec);
	res |= ast_register_application_xml(app_aqm, aqm_exec);
	res |= ast_register_application_xml(app_rqm, rqm_exec);
	res |= ast_register_application_xml(app_pqm, pqm_exec);
	res |= ast_register_application_xml(app_upqm, upqm_exec);
	res |= ast_register_application_xml(app_ql, ql_exec);
	res |= ast_manager_register_xml("Queues", 0, manager_queues_show);
	res |= ast_manager_register_xml("QueueStatus", 0, manager_queues_status);
	res |= ast_manager_register_xml("QueueSummary", 0, manager_queues_summary);
	res |= ast_manager_register_xml("QueueAdd", EVENT_FLAG_AGENT, manager_add_queue_member);
	res |= ast_manager_register_xml("QueueRemove", EVENT_FLAG_AGENT, manager_remove_queue_member);
	res |= ast_manager_register_xml("QueuePause", EVENT_FLAG_AGENT, manager_pause_queue_member);
	res |= ast_manager_register_xml("QueueCallInuse", EVENT_FLAG_AGENT, manager_set_callinuse_queue_member);
	res |= ast_manager_register_xml("QueueLog", EVENT_FLAG_AGENT, manager_queue_log_custom);
	res |= ast_manager_register_xml("QueuePenalty", EVENT_FLAG_AGENT, manager_queue_member_penalty);
	res |= ast_manager_register_xml("QueueRule", 0, manager_queue_rule_show);
	res |= ast_manager_register_xml("QueueReload", 0, manager_queue_reload);
	res |= ast_manager_register_xml("QueueReset", 0, manager_queue_reset);
	res |= ast_custom_function_register(&queuevar_function);
	res |= ast_custom_function_register(&queueexists_function);
	res |= ast_custom_function_register(&queuemembercount_function);
	res |= ast_custom_function_register(&queuememberlist_function);
	res |= ast_custom_function_register(&queuewaitingcount_function);
	res |= ast_custom_function_register(&queuememberpenalty_function);

	if (!(devicestate_tps = ast_taskprocessor_get("app_queue", 0))) {
		ast_log(LOG_WARNING, "devicestate taskprocessor reference failed - devicestate notifications will not occur\n");
	}

	/* in the following subscribe call, do I use DEVICE_STATE, or DEVICE_STATE_CHANGE? */
	if (!(device_state_sub = ast_event_subscribe(AST_EVENT_DEVICE_STATE, device_state_cb, "AppQueue Device state", NULL, AST_EVENT_IE_END))) {
		res = -1;
	}

	ast_extension_state_add(NULL, NULL, extension_state_cb, NULL);

	ast_realtime_require_field("queue_members", "paused", RQ_INTEGER1, 1, "uniqueid", RQ_UINTEGER2, 5, SENTINEL);

	return res ? AST_MODULE_LOAD_DECLINE : 0;
}

static int reload(void)
{
	struct ast_flags mask = {AST_FLAGS_ALL & ~QUEUE_RESET_STATS,};
	ast_unload_realtime("queue_members");
	reload_handler(1, &mask, NULL);
	return 0;
}

static char *queue_refshow(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	struct call_queue *q;
	struct queue_data *qinf;
	struct member *mem;
	struct mem_state *device;
	struct ast_str *out = ast_str_alloca(240);
	struct ao2_iterator queue_iter;
	struct ao2_iterator mem_iter;
	struct ao2_iterator dev_iter;
	struct ao2_iterator qdev_iter;

	switch ( cmd ) {
	case CLI_INIT:
		e->command = "queue ref";
		e->usage =
			"Usage: queue ref\n"
			"       Provides summary of ref's\n";
		return NULL;
	case CLI_GENERATE:
		return complete_queue_show(a->line, a->word, a->pos, a->n);	
	}

	if (a->argc != 2) {
		return CLI_SHOWUSAGE;
	}

	queue_iter = ao2_iterator_init(queues, 0);
	while ((q = ao2_iterator_next(&queue_iter))) {
		ao2_lock(q);
		ao2_lock(q->data);
		ast_str_set(&out, 0, "%s has %d ref stats hash %d", q->name, (ao2_ref(q, 0) - 1), q->data->qhash);
		ao2_unlock(q->data);
		do_print(NULL, a->fd, ast_str_buffer(out));

		if (!ao2_container_count(q->data->members)) {
			do_print(NULL, a->fd, "   No Members");
		} else {
			do_print(NULL, a->fd, "   Members: ");
			mem_iter = ao2_iterator_init(q->data->members, 0);
			while ((mem = ao2_iterator_next(&mem_iter))) {
				ast_str_set(&out, 0, "      %s (%s) has %d ref device %s has %d ref", mem->interface, mem->membername, (ao2_ref(mem, 0) -1), mem->device->state_interface, (ao2_ref(mem->device, 0) - 1));
				do_print(NULL, a->fd, ast_str_buffer(out));
				ao2_ref(mem, -1);
			}
			ao2_iterator_destroy(&mem_iter);
		}
		ao2_unlock(q);
		AST_LIST_LOCK(q->data->head);
		if (!AST_LIST_FIRST(q->data->head)) {
			do_print(NULL, a->fd, "   No Callers");
		} else {
			struct queue_ent *qe;
			int pos = 0;
			AST_LIST_TRAVERSE(q->data->head, qe, next) {
				pos++;
			}
			ast_str_set(&out, 0, "Callers: %d", pos);
			do_print(NULL, a->fd, ast_str_buffer(out));
		}
		AST_LIST_UNLOCK(q->data->head);
		do_print(NULL, a->fd, "");	/* blank line between entries */
		ao2_t_ref(q, -1, "Done with iterator"); /* Unref the iterator's reference */
	}
	ao2_iterator_destroy(&queue_iter);

	do_print(NULL, a->fd, "");	/* blank line between entries */

	if (!ao2_container_count(devices)) {
		do_print(NULL, a->fd, "   No Devices");
	} else {
		do_print(NULL, a->fd, "   Devices: ");
		dev_iter = ao2_iterator_init(devices, 0);
		while ((device = ao2_iterator_next(&dev_iter))) {
			ast_str_set(&out, 0, "%s has %d ref %d reservered %d active", 
				device->state_interface, (ao2_ref(device, 0) -2), device->reserved, device->active);
			do_print(NULL, a->fd, ast_str_buffer(out));
			ao2_ref(device, -1);
		}
		ao2_iterator_destroy(&dev_iter);
	}

	do_print(NULL, a->fd, "");	/* blank line between entries */

	if (!ao2_container_count(qdata)) {
		do_print(NULL, a->fd, "   No Queue Stats");
	} else {
		do_print(NULL, a->fd, "   Queue Stats: ");
		qdev_iter = ao2_iterator_init(qdata, 0);
		while ((qinf = ao2_iterator_next(&qdev_iter))) {
			ast_str_set(&out, 0, "queue %d has %d ref", 
				qinf->qhash, (ao2_ref(qinf, 0) -2));
			do_print(NULL, a->fd, ast_str_buffer(out));
			ao2_ref(qinf, -1);
		}
		ao2_iterator_destroy(&qdev_iter);
	}

	return CLI_SUCCESS;
}

AST_MODULE_INFO(ASTERISK_GPL_KEY, AST_MODFLAG_LOAD_ORDER, "True Call Queueing",
		.load = load_module,
		.unload = unload_module,
		.reload = reload,
		.load_pri = AST_MODPRI_DEVSTATE_CONSUMER,
		.nonoptreq = "res_monitor",
	       );

