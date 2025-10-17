// ICPC Management System - ACMOJ 1986
#include <bits/stdc++.h>
using namespace std;

enum class JudgeStatus { Accepted, Wrong_Answer, Runtime_Error, Time_Limit_Exceed };

struct SubmissionRecord {
    int problemIndex;
    JudgeStatus status;
    int time;
    long long seq; // to break ties when times equal
};

struct FrozenProblemState {
    int preFreezeWrong = 0; // wrong attempts before freeze (on unsolved problems)
    vector<pair<JudgeStatus,int>> submissions; // after freeze submissions
};

struct ProblemState {
    bool solved = false;
    int acceptTime = 0; // time of first AC if solved
    int wrongBeforeAC = 0; // number of wrong attempts before first AC
    int wrongUnsolved = 0; // current wrong attempts when not solved (visible outside freeze)

    // Freeze-cycle state
    FrozenProblemState freeze;
};

struct Team {
    string name;
    vector<ProblemState> probs; // size M after START
    vector<int> solveTimes; // times of solved problems
    vector<int> solveTimesDesc; // cached sorted desc
    bool solveTimesDirty = true;
    int solvedCount = 0;
    long long totalPenalty = 0;

    // For queries
    vector<SubmissionRecord> submissions; // all submissions in order

    // Count of problems that have frozen submissions in current freeze cycle
    int frozenCount = 0;

    // Count of problems that have frozen submissions in current freeze cycle
    int frozenCount = 0;

    bool hasFrozenProblems() const {
        for (const auto &p : probs) {
            if (!p.solved && !p.freeze.submissions.empty()) return true;
            if (!p.solved && p.freeze.preFreezeWrong >= 0 && !p.freeze.submissions.empty()) return true;
        }
        return false;
    }

    void addSolve(int time) {
        solvedCount++;
        totalPenalty += time;
        solveTimes.push_back(time);
        solveTimesDirty = true;
    }

    const vector<int>& getSolveTimesDesc() {
        if (solveTimesDirty) {
            solveTimesDesc = solveTimes;
            sort(solveTimesDesc.begin(), solveTimesDesc.end(), greater<int>());
            solveTimesDirty = false;
        }
        return solveTimesDesc;
    }
};

// Global state
static bool started = false;
static bool frozen = false;
static int durationTime = 0;
static int problemCountM = 0;
static long long globalSeq = 0;

static vector<string> teamNames; // keep names
static unordered_map<string,int> nameToId;
static vector<Team> teams;

// For ranking after last flush
static bool hasFlushed = false;
static vector<int> lastFlushedOrder; // team indices in rank order

// Helpers
static inline bool isWrong(JudgeStatus s) {
    return s == JudgeStatus::Wrong_Answer || s == JudgeStatus::Runtime_Error || s == JudgeStatus::Time_Limit_Exceed;
}

static JudgeStatus parseStatus(const string &s) {
    if (s == "Accepted") return JudgeStatus::Accepted;
    if (s == "Wrong_Answer") return JudgeStatus::Wrong_Answer;
    if (s == "Runtime_Error") return JudgeStatus::Runtime_Error;
    // default
    return JudgeStatus::Time_Limit_Exceed;
}

static string statusToString(JudgeStatus s) {
    switch (s) {
        case JudgeStatus::Accepted: return "Accepted";
        case JudgeStatus::Wrong_Answer: return "Wrong_Answer";
        case JudgeStatus::Runtime_Error: return "Runtime_Error";
        case JudgeStatus::Time_Limit_Exceed: return "Time_Limit_Exceed";
    }
    return "";
}

// Comparator for ranking (current state of teams)
static bool betterTeam(int a, int b) {
    const Team &A = teams[a], &B = teams[b];
    if (A.solvedCount != B.solvedCount) return A.solvedCount > B.solvedCount;
    if (A.totalPenalty != B.totalPenalty) return A.totalPenalty < B.totalPenalty;
    const auto &At = const_cast<Team&>(A).getSolveTimesDesc();
    const auto &Bt = const_cast<Team&>(B).getSolveTimesDesc();
    size_t len = min(At.size(), Bt.size());
    for (size_t i = 0; i < len; ++i) {
        if (At[i] != Bt[i]) return At[i] < Bt[i]; // smaller max solve time ranks higher
    }
    if (At.size() != Bt.size()) return At.size() > Bt.size();
    return A.name < B.name;
}

static vector<int> computeOrderAllTeams() {
    vector<int> order(teams.size());
    iota(order.begin(), order.end(), 0);
    stable_sort(order.begin(), order.end(), [](int a, int b){ return betterTeam(a,b); });
    return order;
}

static void bubbleUp(int &pos, vector<int> &order) {
    while (pos > 0) {
        int cur = order[pos];
        int prev = order[pos - 1];
        if (betterTeam(cur, prev)) {
            swap(order[pos], order[pos - 1]);
            pos--;
        } else {
            break;
        }
    }
}

static void recomputeLastFlushedOrderLexIfNeeded() {
    lastFlushedOrder.resize(teams.size());
    iota(lastFlushedOrder.begin(), lastFlushedOrder.end(), 0);
    stable_sort(lastFlushedOrder.begin(), lastFlushedOrder.end(), [](int a, int b){ return teams[a].name < teams[b].name; });
}

static void printScoreboard(const vector<int> &order, bool showFrozenCells) {
    for (size_t i = 0; i < order.size(); ++i) {
        const Team &T = teams[order[i]];
        int ranking = (int)i + 1;
        cout << T.name << ' ' << ranking << ' ' << T.solvedCount << ' ' << T.totalPenalty;
        for (int p = 0; p < problemCountM; ++p) {
            const ProblemState &PS = T.probs[p];
            cout << ' ';
            if (PS.solved) {
                if (PS.wrongBeforeAC == 0) cout << '+';
                else cout << '+' << PS.wrongBeforeAC;
            } else {
                if (showFrozenCells && frozen && !PS.freeze.submissions.empty()) {
                    int x = PS.freeze.preFreezeWrong;
                    int y = (int)PS.freeze.submissions.size();
                    if (x == 0) cout << "0/" << y;
                    else cout << '-' << x << '/' << y;
                } else {
                    int x = PS.wrongUnsolved;
                    if (x == 0) cout << '.';
                    else cout << '-' << x;
                }
            }
        }
        cout << '\n';
    }
}

static void handleAddTeam(const string &teamName) {
    if (started) {
        cout << "[Error]Add failed: competition has started.\n";
        return;
    }
    if (nameToId.count(teamName)) {
        cout << "[Error]Add failed: duplicated team name.\n";
        return;
    }
    int id = (int)teams.size();
    nameToId[teamName] = id;
    Team T;
    T.name = teamName;
    teams.push_back(move(T));
    teamNames.push_back(teamName);
    cout << "[Info]Add successfully.\n";
}

static void handleStart(int duration_time, int problem_count) {
    if (started) {
        cout << "[Error]Start failed: competition has started.\n";
        return;
    }
    started = true;
    durationTime = duration_time;
    problemCountM = problem_count;
    for (auto &T : teams) {
        T.probs.assign(problemCountM, ProblemState());
        T.solveTimes.clear();
        T.solveTimesDesc.clear();
        T.solveTimesDirty = true;
        T.solvedCount = 0;
        T.totalPenalty = 0;
    }
    hasFlushed = false;
    lastFlushedOrder.clear();
    cout << "[Info]Competition starts.\n";
}

static void handleSubmit(int problemIndex, const string &teamName, JudgeStatus status, int time) {
    int id = nameToId[teamName];
    Team &T = teams[id];
    T.submissions.push_back(SubmissionRecord{problemIndex, status, time, globalSeq++});

    ProblemState &PS = T.probs[problemIndex];
    if (PS.solved) {
        return;
    }
    if (!frozen) {
        if (status == JudgeStatus::Accepted) {
            PS.solved = true;
            PS.acceptTime = time;
            PS.wrongBeforeAC = PS.wrongUnsolved;
            T.totalPenalty += (long long)PS.wrongBeforeAC * 20 + PS.acceptTime;
            T.solveTimes.push_back(PS.acceptTime);
            T.solveTimesDirty = true;
            T.solvedCount++;
        } else if (isWrong(status)) {
            PS.wrongUnsolved++;
        }
    } else {
        // During freeze, only track submissions for problems that were unsolved at freeze time
        if (!PS.solved) {
            if (PS.freeze.submissions.empty()) {
                T.frozenCount++;
            }
            PS.freeze.submissions.emplace_back(status, time);
        }
    }
}

static void handleFlush() {
    cout << "[Info]Flush scoreboard.\n";
    lastFlushedOrder = computeOrderAllTeams();
    hasFlushed = true;
}

static void handleFreeze() {
    if (frozen) {
        cout << "[Error]Freeze failed: scoreboard has been frozen.\n";
        return;
    }
    frozen = true;
    for (auto &T : teams) {
        T.frozenCount = 0;
        for (auto &PS : T.probs) {
            PS.freeze.preFreezeWrong = PS.solved ? 0 : PS.wrongUnsolved;
            PS.freeze.submissions.clear();
        }
    }
    cout << "[Info]Freeze scoreboard.\n";
}

static void applyUnfreezeFor(Team &T, int pidx) {
    ProblemState &PS = T.probs[pidx];
    if (PS.solved) {
        PS.freeze.submissions.clear();
        return;
    }
    bool hadFrozen = !PS.freeze.submissions.empty();
    int wrongBefore = PS.wrongUnsolved; // equals PS.freeze.preFreezeWrong at start
    for (auto &ev : PS.freeze.submissions) {
        if (PS.solved) break;
        JudgeStatus st = ev.first;
        int tim = ev.second;
        if (st == JudgeStatus::Accepted) {
            PS.solved = true;
            PS.acceptTime = tim;
            PS.wrongBeforeAC = wrongBefore;
            T.totalPenalty += (long long)PS.wrongBeforeAC * 20 + PS.acceptTime;
            T.solveTimes.push_back(PS.acceptTime);
            T.solveTimesDirty = true;
            T.solvedCount++;
        } else if (isWrong(st)) {
            wrongBefore++;
        }
    }
    if (!PS.solved) {
        PS.wrongUnsolved = wrongBefore;
    }
    PS.freeze.submissions.clear();
    if (hadFrozen && T.frozenCount > 0) T.frozenCount--;
}

static void handleScroll() {
    if (!frozen) {
        cout << "[Error]Scroll failed: scoreboard has not been frozen.\n";
        return;
    }
    cout << "[Info]Scroll scoreboard.\n";

    vector<int> order = computeOrderAllTeams();
    // Scroll begins with an implicit flush
    lastFlushedOrder = order;
    hasFlushed = true;
    printScoreboard(order, /*showFrozenCells=*/true);

    vector<int> posOf(teams.size());
    for (int i = 0; i < (int)order.size(); ++i) posOf[order[i]] = i;

    // Priority queue to always pick the lowest-ranked team that still has frozen problems
    priority_queue<pair<int,int>> pq; // (position, teamId), max-heap so larger position = lower rank first
    for (int tid = 0; tid < (int)teams.size(); ++tid) {
        if (teams[tid].frozenCount > 0) pq.emplace(posOf[tid], tid);
    }

    while (!pq.empty()) {
        auto [posSnapshot, tid] = pq.top(); pq.pop();
        if (teams[tid].frozenCount <= 0) continue; // no longer frozen
        if (posOf[tid] != posSnapshot) { // stale entry, reinsert with updated position
            pq.emplace(posOf[tid], tid);
            continue;
        }

        // Select smallest problem index among this team's frozen problems
        Team &TT = teams[tid];
        int chosenProb = -1;
        for (int p = 0; p < problemCountM; ++p) {
            if (!TT.probs[p].solved && !TT.probs[p].freeze.submissions.empty()) { chosenProb = p; break; }
        }
        if (chosenProb == -1) continue; // nothing to unfreeze, skip

        vector<int> preOrder = order;
        int oldPos = posOf[tid];

        applyUnfreezeFor(TT, chosenProb);

        int curPos = oldPos;
        bubbleUp(curPos, order);
        for (int i = curPos; i <= oldPos; ++i) posOf[order[i]] = i;

        if (curPos < oldPos) {
            string replacedName = teams[preOrder[curPos]].name;
            cout << TT.name << ' ' << replacedName << ' ' << TT.solvedCount << ' ' << TT.totalPenalty << '\n';
        }

        // If this team still has frozen problems, reinsert with updated position
        if (TT.frozenCount > 0) pq.emplace(posOf[tid], tid);
    }

    printScoreboard(order, /*showFrozenCells=*/false);

    // Update last flushed ranking to the final post-scroll order
    lastFlushedOrder = order;
    hasFlushed = true;

    for (auto &T : teams) {
        T.frozenCount = 0;
        for (auto &PS : T.probs) {
            PS.freeze.submissions.clear();
            PS.freeze.preFreezeWrong = 0;
        }
    }
    frozen = false;
}

static void handleQueryRanking(const string &teamName) {
    auto it = nameToId.find(teamName);
    if (it == nameToId.end()) {
        cout << "[Error]Query ranking failed: cannot find the team.\n";
        return;
    }
    int tid = it->second;
    cout << "[Info]Complete query ranking.\n";
    if (frozen) {
        cout << "[Warning]Scoreboard is frozen. The ranking may be inaccurate until it were scrolled.\n";
    }
    if (!hasFlushed) {
        recomputeLastFlushedOrderLexIfNeeded();
    }
    if ((int)lastFlushedOrder.size() != (int)teams.size()) {
        if (hasFlushed) {
            lastFlushedOrder = computeOrderAllTeams();
        } else {
            recomputeLastFlushedOrderLexIfNeeded();
        }
    }
    int rankOut = -1;
    for (int i = 0; i < (int)lastFlushedOrder.size(); ++i) {
        if (lastFlushedOrder[i] == tid) { rankOut = i + 1; break; }
    }
    cout << teamName << " NOW AT RANKING " << rankOut << '\n';
}

static void handleQuerySubmission(const string &teamName, const string &probFilter, const string &statusFilter) {
    auto it = nameToId.find(teamName);
    if (it == nameToId.end()) {
        cout << "[Error]Query submission failed: cannot find the team.\n";
        return;
    }
    int tid = it->second;
    cout << "[Info]Complete query submission.\n";
    int pFilter = -1;
    if (probFilter != "ALL") {
        pFilter = probFilter[0] - 'A';
    }
    int sMask = -1;
    if (statusFilter != "ALL") {
        if (statusFilter == "Accepted") sMask = 0;
        else if (statusFilter == "Wrong_Answer") sMask = 1;
        else if (statusFilter == "Runtime_Error") sMask = 2;
        else sMask = 3;
    }

    const auto &subs = teams[tid].submissions;
    for (int i = (int)subs.size() - 1; i >= 0; --i) {
        const auto &rec = subs[i];
        if (pFilter != -1 && rec.problemIndex != pFilter) continue;
        if (sMask != -1) {
            int code = 0;
            switch (rec.status) {
                case JudgeStatus::Accepted: code = 0; break;
                case JudgeStatus::Wrong_Answer: code = 1; break;
                case JudgeStatus::Runtime_Error: code = 2; break;
                case JudgeStatus::Time_Limit_Exceed: code = 3; break;
            }
            if (code != sMask) continue;
        }
        char probChar = char('A' + rec.problemIndex);
        cout << teamName << ' ' << probChar << ' ' << statusToString(rec.status) << ' ' << rec.time << '\n';
        return;
    }
    cout << "Cannot find any submission.\n";
}

int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string cmd;
    while (true) {
        if (!(cin >> cmd)) break;
        if (cmd == "ADDTEAM") {
            string teamName; cin >> teamName;
            handleAddTeam(teamName);
        } else if (cmd == "START") {
            string t1, t2; // DURATION, PROBLEM
            int dur, pc;
            cin >> t1 >> dur >> t2 >> pc;
            handleStart(dur, pc);
        } else if (cmd == "SUBMIT") {
            string probName; string by; string teamName; string with; string statusStr; string at; int time;
            cin >> probName >> by >> teamName >> with >> statusStr >> at >> time;
            int pidx = probName[0] - 'A';
            handleSubmit(pidx, teamName, parseStatus(statusStr), time);
        } else if (cmd == "FLUSH") {
            handleFlush();
        } else if (cmd == "FREEZE") {
            handleFreeze();
        } else if (cmd == "SCROLL") {
            handleScroll();
        } else if (cmd == "QUERY_RANKING") {
            string teamName; cin >> teamName;
            handleQueryRanking(teamName);
        } else if (cmd == "QUERY_SUBMISSION") {
            string teamName; cin >> teamName; // WHERE PROBLEM=... AND STATUS=...
            string where, problemEq, problemVal, andWord, statusEq, statusVal;
            cin >> where; // WHERE
            cin >> problemEq; // PROBLEM=...
            if (problemEq.rfind("PROBLEM=",0) == 0) problemVal = problemEq.substr(8);
            else problemVal = "ALL";
            cin >> andWord; // AND
            cin >> statusEq; // STATUS=...
            if (statusEq.rfind("STATUS=",0) == 0) statusVal = statusEq.substr(7);
            else statusVal = "ALL";
            handleQuerySubmission(teamName, problemVal, statusVal);
        } else if (cmd == "END") {
            cout << "[Info]Competition ends.\n";
            break;
        } else {
            // ignore
        }
    }
    return 0;
}
