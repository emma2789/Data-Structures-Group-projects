// ============================================================================
// INF311: Data Structures | Semester Project 1
// University Student Registration System          (Group 1)
// Members: Abdul Karim Appiah, Aboagye Elizabeth, Afful Emmanuel,
//          Afriyie Adwoa Safowaa, Agbofu Wisdom Tetteh
//
// Data structure : AVL TREE (a self-balancing binary search tree) keyed by
//                  student ID. Written from scratch, no STL containers.
// Why a tree      : the main query is "search student by ID", and "display all"
//                  should list students in order. A BST finds an ID in
//                  O(log n) and an in-order walk lists IDs sorted for free.
// Why AVL         : IDs are often handed out in increasing order, which turns
//                  a plain BST into a linked list (O(n) search, recursion
//                  depth n). The AVL rotations keep the height below
//                  1.44 * log2(n), so add, delete, search and update are always
//                  O(log n). Count is O(1) (a counter kept in step).
// Rejected        : sorted array (O(n) insert/delete), linked list (O(n)
//                  search), hash table (O(1) search but display must sort).
//
// Build : g++ -std=c++17 -Wall -Wextra -O2 main.cpp -o registry
// Run   : ./registry          (interactive menu)
//         ./registry --test   (automated tests)
//         ./registry --bench  (timing with 100000 students)
// ============================================================================
#include <chrono>
#include <cstdio>
#include <iomanip>
#include <iostream>
#include <string>

using std::cout;
using std::string;

struct Student { string id, name, programme; int level; };

// ---- Outcome codes: the registry never prints errors, the menu layer does.
enum class Outcome { Ok, EmptyRegistry, DuplicateId, NotFound, InvalidId, InvalidName,
                     InvalidProgramme, InvalidLevel, RegistryFull };

const char* explain(Outcome o) {
    static const char* const text[] = {
        "Done.", "The registry is empty.", "A student with that ID is already registered.",
        "No student with that ID was found.", "Invalid ID. Use 4-15 letters, digits, '/' or '-'.",
        "Invalid name. Use 2-50 letters, spaces, '.', '-' or apostrophes.",
        "Invalid programme. Use 2-40 letters, digits, spaces, '-', '&' or '.'.",
        "Invalid level. Use 100, 200, 300, 400, 500 or 600.", "The registry is full."};
    return text[static_cast<int>(o)];
}

// ---- Input checking helpers
namespace input {
    string trim(const string& s) {
        size_t a = s.find_first_not_of(" \t\r");
        return a == string::npos ? "" : s.substr(a, s.find_last_not_of(" \t\r") - a + 1);
    }
    string cleanId(const string& raw) {                       // trimmed + upper case
        string s = trim(raw);
        for (char& c : s) if (c >= 'a' && c <= 'z') c = char(c - 32);
        return s;
    }
    // True if the length is within [lo, hi] and every character is a letter, a digit
    // (when allowed) or one of the extra characters.
    bool fits(const string& s, size_t lo, size_t hi, bool digits, const string& extra) {
        if (s.size() < lo || s.size() > hi) return false;
        for (char c : s) {
            bool ok = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
                      (digits && c >= '0' && c <= '9') || extra.find(c) != string::npos;
            if (!ok) return false;
        }
        return true;
    }
    bool validId(const string& s)        { return fits(s, 4, 15, true, "/-"); }
    bool validName(const string& s)      { return fits(s, 2, 50, false, " .-'"); }
    bool validProgramme(const string& s) { return fits(s, 2, 40, true, " -&."); }
    bool parseLevel(const string& raw, int& out) {            // 100..600 in steps of 100
        string s = trim(raw);
        if (s.empty() || s.size() > 3) return false;
        int v = 0;
        for (char c : s) { if (c < '0' || c > '9') return false; v = v * 10 + (c - '0'); }
        out = v;
        return v >= 100 && v <= 600 && v % 100 == 0;
    }
}

// ----------------------------------------------------------------------------
// StudentRegistry: the AVL tree and every operation on it
// ----------------------------------------------------------------------------
class StudentRegistry {
    struct Node {
        Student s;
        Node *left = nullptr, *right = nullptr;
        int height = 1;                                       // height of the subtree rooted here
        explicit Node(const Student& x) : s(x) {}
    };
    Node* root_ = nullptr;
    int count_ = 0;
    const int capacity_;

    // ----- AVL machinery -----
    static int ht(const Node* n) { return n ? n->height : 0; }
    static void refresh(Node* n) { int l = ht(n->left), r = ht(n->right); n->height = 1 + (l > r ? l : r); }

    static Node* rotateRight(Node* y) {
        Node* x = y->left;
        y->left = x->right; x->right = y;
        refresh(y); refresh(x);
        return x;
    }
    static Node* rotateLeft(Node* x) {
        Node* y = x->right;
        x->right = y->left; y->left = x;
        refresh(x); refresh(y);
        return y;
    }
    static Node* rebalance(Node* n) {                         // restores |balance| <= 1 at n
        refresh(n);
        int b = ht(n->left) - ht(n->right);
        if (b > 1) {                                          // left heavy
            if (ht(n->left->left) < ht(n->left->right)) n->left = rotateLeft(n->left);     // LR case
            return rotateRight(n);
        }
        if (b < -1) {                                         // right heavy
            if (ht(n->right->right) < ht(n->right->left)) n->right = rotateRight(n->right); // RL case
            return rotateLeft(n);
        }
        return n;
    }

    static Node* insert(Node* n, const Student& s, bool& added) {
        if (!n) { added = true; return new Node(s); }
        if (s.id < n->s.id) n->left = insert(n->left, s, added);
        else if (s.id > n->s.id) n->right = insert(n->right, s, added);
        else return n;                                        // duplicate: added stays false
        return added ? rebalance(n) : n;
    }

    static Node* erase(Node* n, const string& id, bool& removed) {
        if (!n) return nullptr;
        if (id < n->s.id) n->left = erase(n->left, id, removed);
        else if (id > n->s.id) n->right = erase(n->right, id, removed);
        else {
            removed = true;
            if (!n->left || !n->right) {                      // 0 or 1 child: splice the node out
                Node* child = n->left ? n->left : n->right;
                delete n;
                return child;
            }
            Node* m = n->right;                               // 2 children: take the in-order successor
            while (m->left) m = m->left;
            n->s = m->s;
            bool ignore = false;
            n->right = erase(n->right, n->s.id, ignore);
        }
        return removed ? rebalance(n) : n;
    }

    Node* find(const string& id) const {                      // id must already be cleaned
        Node* n = root_;
        while (n && n->s.id != id) n = id < n->s.id ? n->left : n->right;
        return n;
    }

    static void destroy(Node* n) { if (n) { destroy(n->left); destroy(n->right); delete n; } }

    void walk(const Node* n, int& row) const {                // in-order = sorted by ID
        if (!n) return;
        walk(n->left, row);
        cout << " " << std::setw(4) << ++row << "  " << std::left << std::setw(16) << n->s.id
             << std::setw(26) << n->s.name << std::setw(28) << n->s.programme << std::right
             << n->s.level << "\n";
        walk(n->right, row);
    }

    // Returns the subtree height if the subtree is a valid AVL tree, otherwise -1.
    static int verify(const Node* n, const string*& prev, int& nodes) {
        if (!n) return 0;
        int hl = verify(n->left, prev, nodes);
        if (hl < 0) return -1;
        if (prev && !(*prev < n->s.id)) return -1;            // IDs must be strictly increasing
        prev = &n->s.id; ++nodes;
        int hr = verify(n->right, prev, nodes);
        if (hr < 0 || hl - hr > 1 || hr - hl > 1) return -1;  // balance factor within +-1
        int h = 1 + (hl > hr ? hl : hr);
        return h == n->height ? h : -1;                       // stored height must be right
    }

public:
    explicit StudentRegistry(int capacity = 100000) : capacity_(capacity) {}
    StudentRegistry(const StudentRegistry&) = delete;
    StudentRegistry& operator=(const StudentRegistry&) = delete;
    ~StudentRegistry() { destroy(root_); }

    int  count() const { return count_; }
    bool empty() const { return count_ == 0; }
    int  height() const { return ht(root_); }

    // ----- insertion -----
    Outcome add(const string& rawId, const string& rawName, const string& rawProgramme, const string& levelText) {
        Student s{input::cleanId(rawId), input::trim(rawName), input::trim(rawProgramme), 0};
        if (!input::validId(s.id)) return Outcome::InvalidId;
        if (!input::validName(s.name)) return Outcome::InvalidName;
        if (!input::validProgramme(s.programme)) return Outcome::InvalidProgramme;
        if (!input::parseLevel(levelText, s.level)) return Outcome::InvalidLevel;
        if (count_ >= capacity_) return find(s.id) ? Outcome::DuplicateId : Outcome::RegistryFull;
        bool added = false;
        root_ = insert(root_, s, added);                      // one pass finds a duplicate or inserts
        if (!added) return Outcome::DuplicateId;
        ++count_;
        return Outcome::Ok;
    }

    // ----- deletion -----
    Outcome remove(const string& rawId) {
        string id = input::cleanId(rawId);
        if (!input::validId(id)) return Outcome::InvalidId;
        if (empty()) return Outcome::EmptyRegistry;
        bool removed = false;
        root_ = erase(root_, id, removed);
        if (!removed) return Outcome::NotFound;
        --count_;
        return Outcome::Ok;
    }

    // ----- searching -----
    Outcome search(const string& rawId, Student& out) const {
        string id = input::cleanId(rawId);
        if (!input::validId(id)) return Outcome::InvalidId;
        if (empty()) return Outcome::EmptyRegistry;
        const Node* n = find(id);
        if (!n) return Outcome::NotFound;
        out = n->s;
        return Outcome::Ok;
    }

    // ----- update: an empty text means "keep the current value"; nothing changes unless all are valid -----
    Outcome update(const string& rawId, const string& rawName, const string& rawProgramme, const string& levelText) {
        string id = input::cleanId(rawId);
        if (!input::validId(id)) return Outcome::InvalidId;
        if (empty()) return Outcome::EmptyRegistry;
        Node* n = find(id);
        if (!n) return Outcome::NotFound;
        string name = input::trim(rawName), prog = input::trim(rawProgramme);
        int level = n->s.level;
        if (!name.empty() && !input::validName(name)) return Outcome::InvalidName;
        if (!prog.empty() && !input::validProgramme(prog)) return Outcome::InvalidProgramme;
        if (!input::trim(levelText).empty() && !input::parseLevel(levelText, level)) return Outcome::InvalidLevel;
        if (!name.empty()) n->s.name = name;
        if (!prog.empty()) n->s.programme = prog;
        n->s.level = level;
        return Outcome::Ok;
    }

    // ----- traversal / display -----
    Outcome displayAll() const {
        if (empty()) return Outcome::EmptyRegistry;
        cout << "  No.  " << std::left << std::setw(16) << "Student ID" << std::setw(26) << "Name"
             << std::setw(28) << "Programme" << std::right << "Level\n"
             << std::string(82, '-') << "\n";
        int row = 0;
        walk(root_, row);
        cout << "Total registered students: " << count_ << "\n";
        return Outcome::Ok;
    }

    // Debug check used by the tests: valid BST order, valid heights, balanced, count matches.
    bool selfCheck() const {
        const string* prev = nullptr;
        int nodes = 0;
        return verify(root_, prev, nodes) >= 0 && nodes == count_;
    }
};

// ============================================================================
// Menu
// ============================================================================
namespace ui {
    bool ask(const char* prompt, string& out) {              // false when input ends
        cout << prompt;
        return bool(std::getline(std::cin, out));
    }

    void report(Outcome o) { cout << (o == Outcome::Ok ? "[OK] " : "[ERROR] ") << explain(o) << "\n"; }

    void menu(const StudentRegistry& r) {
        cout << "\n==============================================\n"
             << "   UNIVERSITY STUDENT REGISTRATION SYSTEM\n"
             << "   Registered students: " << r.count() << "\n"
             << "==============================================\n"
             << "  1. Add student\n  2. Delete student\n  3. Search student by ID\n"
             << "  4. Display all students\n  5. Update student information\n"
             << "  6. Count registered students\n  7. Load sample students\n  0. Exit\n"
             << "Choose an option: ";
    }

    void loadSample(StudentRegistry& r) {
        const char* rows[][4] = {{"ICT-2401", "Akosua Mensah", "Computer Science", "200"},
                                 {"ICT-2402", "Kwabena Owusu", "Information Technology", "300"},
                                 {"BUS-2417", "Esi Quaye", "Business Administration", "100"},
                                 {"ENG-2409", "Yaw Darko", "Mechanical Engineering", "400"},
                                 {"ICT-2433", "Adwoa Boateng", "Computer Science", "200"}};
        int added = 0;
        for (auto& x : rows) added += r.add(x[0], x[1], x[2], x[3]) == Outcome::Ok;
        cout << "[OK] " << added << " sample student(s) loaded.\n";
    }

    void run(StudentRegistry& r) {
        for (;;) {
            menu(r);
            string line;
            if (!std::getline(std::cin, line)) return;       // end of input behaves like Exit
            line = input::trim(line);
            string id, name, prog, level;
            if (line == "0") { cout << "Goodbye.\n"; return; }
            if (line == "1") {
                if (!ask("Student ID: ", id) || !ask("Full name: ", name) ||
                    !ask("Programme: ", prog) || !ask("Level (100-600): ", level)) return;
                report(r.add(id, name, prog, level));
            } else if (line == "2") {
                if (!ask("Student ID to delete: ", id)) return;
                report(r.remove(id));
            } else if (line == "3") {
                if (!ask("Student ID to search: ", id)) return;
                Student s;
                Outcome o = r.search(id, s);
                if (o != Outcome::Ok) report(o);
                else cout << "Found:\n  ID: " << s.id << "\n  Name: " << s.name
                          << "\n  Programme: " << s.programme << "\n  Level: " << s.level << "\n";
            } else if (line == "4") {
                Outcome o = r.displayAll();
                if (o != Outcome::Ok) report(o);
            } else if (line == "5") {
                if (!ask("Student ID to update: ", id) || !ask("New name (Enter to keep): ", name) ||
                    !ask("New programme (Enter to keep): ", prog) || !ask("New level (Enter to keep): ", level)) return;
                report(r.update(id, name, prog, level));
            } else if (line == "6") {
                cout << "Registered students: " << r.count() << "\n";
            } else if (line == "7") {
                loadSample(r);
            } else {
                cout << "[ERROR] Invalid option. Enter a number from the menu.\n";
            }
        }
    }
}

// ============================================================================
// Automated tests (run with --test)
// ============================================================================
namespace tests {
    using O = Outcome;
    int passed = 0, failed = 0;

    void check(bool ok, const char* what) {
        ++(ok ? passed : failed);
        cout << (ok ? "  [PASS] " : "  [FAIL] ") << what << "\n";
    }
    string idOf(int i) { char b[16]; std::snprintf(b, sizeof b, "ID%08d", i); return b; }
    O put(StudentRegistry& r, int i) { return r.add(idOf(i), "Test Student", "Computer Science", "100"); }

    void emptyRegistry() {
        cout << "\nGROUP 1: Empty registry\n";
        StudentRegistry r;
        Student s;
        check(r.count() == 0 && r.empty() && r.selfCheck(), "a new registry holds 0 students");
        check(r.remove("ICT-2401") == O::EmptyRegistry, "delete on an empty registry");
        check(r.search("ICT-2401", s) == O::EmptyRegistry, "search on an empty registry");
        check(r.update("ICT-2401", "X Y", "", "") == O::EmptyRegistry, "update on an empty registry");
        check(r.displayAll() == O::EmptyRegistry, "display on an empty registry");
    }

    void normalUse() {
        cout << "\nGROUP 2: Normal operations\n";
        StudentRegistry r;
        Student s;
        check(r.add("ICT-2401", "Akosua Mensah", "Computer Science", "200") == O::Ok, "add first student");
        check(r.add("ICT-2402", "Kwabena Owusu", "Information Technology", "300") == O::Ok, "add second student");
        check(r.add("BUS-2417", "Esi Quaye", "Business Administration", "100") == O::Ok, "add third student");
        check(r.add("ENG-2409", "Yaw Darko", "Mechanical Engineering", "400") == O::Ok, "add fourth student");
        check(r.add("ICT-2433", "Adwoa Boateng", "Computer Science", "200") == O::Ok, "add fifth student");
        check(r.count() == 5 && r.selfCheck(), "count is 5 and the tree is valid");
        check(r.search("ICT-2402", s) == O::Ok && s.name == "Kwabena Owusu" && s.level == 300, "search returns the right record");
        check(r.search("  ict-2402 ", s) == O::Ok && s.id == "ICT-2402", "ID search ignores letter case and spaces");
        check(r.update("ICT-2402", "Kwabena K. Owusu", "", "") == O::Ok && r.search("ICT-2402", s) == O::Ok &&
              s.name == "Kwabena K. Owusu" && s.programme == "Information Technology", "update name only keeps other fields");
        check(r.update("ICT-2402", "", "Computer Science", "400") == O::Ok && r.search("ICT-2402", s) == O::Ok &&
              s.programme == "Computer Science" && s.level == 400, "update programme and level");
        check(r.remove("BUS-2417") == O::Ok && r.count() == 4 && r.selfCheck(), "delete a student");
        check(r.search("BUS-2417", s) == O::NotFound, "deleted student can no longer be found");
        check(r.displayAll() == O::Ok, "display all succeeds");
    }

    void invalidInput() {
        cout << "\nGROUP 3: Invalid input\n";
        StudentRegistry r;
        Student s;
        const char* good[] = {"ICT-2401", "Ama Serwaa", "Computer Science", "200"};
        check(r.add("", good[1], good[2], good[3]) == O::InvalidId, "empty ID refused");
        check(r.add("AB1", good[1], good[2], good[3]) == O::InvalidId, "3-character ID refused");
        check(r.add(string(16, 'A'), good[1], good[2], good[3]) == O::InvalidId, "16-character ID refused");
        check(r.add("AB CD1", good[1], good[2], good[3]) == O::InvalidId, "ID with a space refused");
        check(r.add("AB@12", good[1], good[2], good[3]) == O::InvalidId, "ID with a symbol refused");
        check(r.add(good[0], "A", good[2], good[3]) == O::InvalidName, "1-character name refused");
        check(r.add(good[0], string(51, 'a'), good[2], good[3]) == O::InvalidName, "51-character name refused");
        check(r.add(good[0], "J0hn Doe", good[2], good[3]) == O::InvalidName, "name with a digit refused");
        check(r.add(good[0], "   ", good[2], good[3]) == O::InvalidName, "blank name refused");
        check(r.add(good[0], good[1], "C", good[3]) == O::InvalidProgramme, "1-character programme refused");
        check(r.add(good[0], good[1], "CS;DROP", good[3]) == O::InvalidProgramme, "programme with a symbol refused");
        check(r.add(good[0], good[1], good[2], "0") == O::InvalidLevel, "level 0 refused");
        check(r.add(good[0], good[1], good[2], "150") == O::InvalidLevel, "level 150 refused");
        check(r.add(good[0], good[1], good[2], "700") == O::InvalidLevel, "level 700 refused");
        check(r.add(good[0], good[1], good[2], "abc") == O::InvalidLevel, "non-numeric level refused");
        check(r.add(good[0], good[1], good[2], "") == O::InvalidLevel, "empty level refused");
        check(r.add(good[0], good[1], good[2], "-100") == O::InvalidLevel, "negative level refused");
        check(r.count() == 0, "no invalid record was stored");
        r.add(good[0], good[1], good[2], good[3]);
        check(r.search("??", s) == O::InvalidId && r.remove("??") == O::InvalidId && r.update("??", "", "", "") == O::InvalidId,
              "search, delete and update refuse a malformed ID");
    }

    void duplicatesAndMissing() {
        cout << "\nGROUP 4: Duplicates and non-existent records\n";
        StudentRegistry r;
        Student s;
        r.add("ICT-2401", "Ama Serwaa", "Computer Science", "200");
        check(r.add("ICT-2401", "Other Person", "Physics", "100") == O::DuplicateId, "same ID twice refused");
        check(r.add("  ict-2401  ", "Other Person", "Physics", "100") == O::DuplicateId, "same ID in other case and padding refused");
        check(r.count() == 1 && r.search("ICT-2401", s) == O::Ok && s.name == "Ama Serwaa", "the original record is untouched");
        check(r.remove("ICT-9999") == O::NotFound, "delete of a missing ID");
        check(r.search("ICT-9999", s) == O::NotFound, "search for a missing ID");
        check(r.update("ICT-9999", "New Name", "", "") == O::NotFound, "update of a missing ID");
        check(r.update("ICT-2401", "Bad1 Name", "Physics", "300") == O::InvalidName, "update with an invalid name is refused");
        check(r.search("ICT-2401", s) == O::Ok && s.programme == "Computer Science" && s.level == 200,
              "a refused update changes nothing");
        check(r.update("ICT-2401", "", "", "250") == O::InvalidLevel, "update with an invalid level is refused");
    }

    void boundaries() {
        cout << "\nGROUP 5: Boundary cases\n";
        StudentRegistry r;
        Student s;
        check(r.add("ABCD", "Ab", "Ab", "100") == O::Ok, "shortest ID, name and programme and level 100");
        check(r.add(string(15, 'Z'), string(50, 'n'), string(40, 'p'), "600") == O::Ok, "longest ID, name and programme and level 600");
        check(r.count() == 2 && r.selfCheck(), "both boundary students stored");
        check(r.remove("ABCD") == O::Ok && r.remove(string(15, 'z')) == O::Ok && r.empty(), "deleting every student empties the registry");
        check(r.search("ABCD", s) == O::EmptyRegistry, "registry behaves as empty again");
        check(r.add("ICT-1000", "Again Student", "Computer Science", "100") == O::Ok && r.count() == 1, "registry is reusable after emptying");
        StudentRegistry small(3);
        small.add("ID01", "Aa Bb", "CS", "100"); small.add("ID02", "Aa Bb", "CS", "100"); small.add("ID03", "Aa Bb", "CS", "100");
        check(small.add("ID04", "Aa Bb", "CS", "100") == O::RegistryFull, "overflow: a full registry refuses a new student");
        check(small.add("ID02", "Aa Bb", "CS", "100") == O::DuplicateId, "a duplicate is still reported when the registry is full");
        check(small.remove("ID01") == O::Ok && small.add("ID04", "Aa Bb", "CS", "100") == O::Ok, "space freed by a delete can be used again");
    }

    void treeShapes() {
        cout << "\nGROUP 6: AVL balancing and deletion cases\n";
        {   StudentRegistry r;  for (int i = 1; i <= 3; ++i) put(r, i);
            check(r.selfCheck() && r.height() == 2, "ascending inserts (right-right case) rotate to height 2"); }
        {   StudentRegistry r;  for (int i = 3; i >= 1; --i) put(r, i);
            check(r.selfCheck() && r.height() == 2, "descending inserts (left-left case) rotate to height 2"); }
        {   StudentRegistry r;  put(r, 3); put(r, 1); put(r, 2);
            check(r.selfCheck() && r.height() == 2, "left-right case rotates to height 2"); }
        {   StudentRegistry r;  put(r, 1); put(r, 3); put(r, 2);
            check(r.selfCheck() && r.height() == 2, "right-left case rotates to height 2"); }
        {   StudentRegistry r;  for (int i = 1; i <= 15; ++i) put(r, i);
            check(r.height() == 4 && r.selfCheck(), "15 ascending inserts give a perfect tree of height 4");
            check(r.remove(idOf(1)) == O::Ok && r.selfCheck(), "delete a leaf");
            check(r.remove(idOf(2)) == O::Ok && r.selfCheck(), "delete a node with one child or after rebalancing");
            check(r.remove(idOf(4)) == O::Ok && r.selfCheck(), "delete a node with two children");
            check(r.remove(idOf(8)) == O::Ok && r.selfCheck(), "delete the root");
            check(r.count() == 11, "count is 11 after four deletions"); }
    }

    void largeInput() {
        cout << "\nGROUP 7: Large input (20000 students, ascending IDs)\n";
        StudentRegistry r;
        const int N = 20000;
        bool ok = true;
        for (int i = 1; i <= N; ++i) ok = ok && put(r, i) == O::Ok;
        check(ok && r.count() == N, "20000 students added");
        check(r.selfCheck(), "tree is a valid AVL tree");
        check(r.height() <= 20, "height stays about log2(n): at most 20 for 20000 students");
        Student s;
        ok = true;
        for (int i = 1; i <= N; ++i) ok = ok && r.search(idOf(i), s) == O::Ok && s.id == idOf(i);
        check(ok, "every one of the 20000 students can be found");
        ok = true;
        for (int i = 1; i <= N; i += 2) ok = ok && r.remove(idOf(i)) == O::Ok;
        check(ok && r.count() == N / 2 && r.selfCheck(), "deleting every second student leaves 10000 and a valid tree");
        ok = true;
        for (int i = 1; i <= N; ++i) ok = ok && ((r.search(idOf(i), s) == O::Ok) == (i % 2 == 0));
        check(ok, "only the even-numbered students remain");
    }

    void randomStress() {
        cout << "\nGROUP 8: Random adds and deletes against a simple model\n";
        StudentRegistry r;
        bool present[1000] = {false};
        int model = 0;
        unsigned long long x = 424242;
        auto next = [&](int m) { x = x * 6364136223846793005ULL + 1442695040888963407ULL; return int((x >> 33) % m); };
        bool ok = true;
        for (int step = 0; step < 20000; ++step) {
            int i = next(1000);
            if (next(2)) {
                Outcome want = present[i] ? O::DuplicateId : O::Ok;
                ok = ok && put(r, i) == want;
                if (!present[i]) { present[i] = true; ++model; }
            } else {
                Outcome want = model == 0 ? O::EmptyRegistry : (present[i] ? O::Ok : O::NotFound);
                ok = ok && r.remove(idOf(i)) == want;
                if (present[i]) { present[i] = false; --model; }
            }
        }
        check(ok, "20000 random operations all give the expected result");
        check(r.count() == model && r.selfCheck(), "final count matches the model and the tree is valid");
    }

    void runAll() {
        emptyRegistry(); normalUse(); invalidInput(); duplicatesAndMissing();
        boundaries(); treeShapes(); largeInput(); randomStress();
        cout << "\n--------------------------------------------\n"
             << "TOTAL: " << passed << " passed, " << failed << " failed\n";
    }
}

// ============================================================================
// Timing (run with --bench)
// ============================================================================
namespace bench {
    void run() {
        using clk = std::chrono::steady_clock;
        const int N = 100000;
        StudentRegistry r(2 * N);
        Student s;
        auto t = clk::now();
        auto lap = [&](const char* what) {
            std::printf("  %-44s %8.1f ms\n", what, std::chrono::duration<double, std::milli>(clk::now() - t).count());
            t = clk::now();
        };
        std::printf("Timing with %d students (IDs added in increasing order, the worst case for a plain BST)\n", N);
        for (int i = 1; i <= N; ++i) tests::put(r, i);
        lap("add 100000 students");
        std::printf("  tree height %d (a plain BST would be %d)\n", r.height(), N);
        for (int i = 1; i <= N; ++i) r.search(tests::idOf(i), s);
        lap("search 100000 students by ID");
        for (int i = 1; i <= N; ++i) r.update(tests::idOf(i), "Updated Name", "", "300");
        lap("update 100000 students");
        for (int i = 1; i <= N; i += 2) r.remove(tests::idOf(i));
        lap("delete 50000 students");
        std::printf("  left: %d students, tree valid: %s\n", r.count(), r.selfCheck() ? "yes" : "NO");
    }
}

int main(int argc, char** argv) {
    string mode = argc > 1 ? argv[1] : "";
    if (mode == "--test") { tests::runAll(); return tests::failed == 0 ? 0 : 1; }
    if (mode == "--bench") { bench::run(); return 0; }
    StudentRegistry registry;
    ui::run(registry);
    return 0;
}
