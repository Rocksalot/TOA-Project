#include <iostream>
#include <string>
#include <vector>
#include <map>
#include <random>
#include <ctime>
#include <algorithm>
#include <fstream>
#include <sstream>
#include <chrono>
#include <set>
#include <queue>

using namespace std;

void replaceStringWithVector(vector<string>& mainVec, const string& toFind,string& replacementVec)                    
{
    auto it = find(mainVec.begin(), mainVec.end(), toFind);
    if (it != mainVec.end()) 
    {
        it = mainVec.erase(it);
        mainVec.insert(it, replacementVec);
    }
}

struct Production 
{
    string lhs;
    vector<string> rhs; // Each rule is a sequence of symbols (terminals or non-terminals) 
};

class CFG {
private:
    map<string, Production> rules;
    string startSymbol;
    string augmentedStart;

    struct State 
    {
        string lhs;
        vector<string> rhs;
        int dot;
        int start;
        bool operator<(State const &other) const 
        {
            if (lhs != other.lhs) return lhs < other.lhs;
            if (rhs != other.rhs) return rhs < other.rhs;
            if (dot != other.dot) return dot < other.dot;
            return start < other.start;
        }
    };

public:
    CFG(const string& start) : startSymbol(start)  // reminder to modify filling so that augmentedStart is accounted for
    {
        augmentedStart = startSymbol + "'";
        rules[augmentedStart] = {augmentedStart, {startSymbol}};
    }

    void addRule(const string& lhs, const vector<string>& alternatives) 
    {
        rules[lhs] = { lhs, alternatives };
    }

    string generateString(int maxDepth = 5) 
    {
        string result;
        map<string,Production> checked;
        vector<string> symbols;
        try_again:
        symbols = {startSymbol};
        result = derive(symbols, checked, maxDepth);
        if(result == "E")
        {
            symbols.clear();
            checked.clear();
            goto try_again;
        }
        
        return result;
    }

    bool isValidString(const string& input) 
    {
        int n = input.size();
        vector< set<State> > chart(n+1);
        vector< queue<State> > work(n+1);

        auto addState = [&](int idx, State const &st) 
        {
            if (!chart[idx].count(st)) 
            {
                chart[idx].insert(st);
                work[idx].push(st);
            }
        };

        vector<string> initRhs = tokenize(rules[augmentedStart].rhs[0]);
        addState(0, State{augmentedStart, initRhs, 0, 0});

        for (int i = 0; i <= n; ++i)
        {
            while (!work[i].empty()) 
            {
                State s = work[i].front(); 
                work[i].pop();
                if (s.dot < (int)s.rhs.size()) 
                {
                    string nextSym = s.rhs[s.dot];
                    if (rules.count(nextSym))
                    {
                        for (auto &alt : rules[nextSym].rhs) 
                        {
                            vector<string> tokens = tokenize(alt);
                            addState(i, State{nextSym, tokens, 0, i});
                        }
                    }
                    else if (i < n && nextSym.size() == 1 && input[i] == nextSym[0]) 
                    {
                        State scan = s;
                        scan.dot++;
                        addState(i+1, scan);
                    }
                } 
                else 
                {
                    for (auto &st2 : chart[s.start]) 
                    {
                        if (st2.dot < (int)st2.rhs.size() && st2.rhs[st2.dot] == s.lhs) 
                        {
                            State comp = st2;
                            comp.dot++;
                            addState(i, comp);
                        }
                    }
                }
            }
        }

        vector<string> finalRhs = tokenize(rules[augmentedStart].rhs[0]);
        State finalState{augmentedStart, finalRhs, 1, 0};
        return chart[n].count(finalState) > 0;
    }

    vector<string> deriveLeftmost(const string& input) 
    {
        using Form = vector<string>;
        struct Node { Form form; vector<Form> path; };
        auto tokenize = [&](const string &alt) 
        {
            Form t;
            for (char c: alt) t.push_back(string(1, c));
            return t;
        };
        string target = input;
        Form start = { startSymbol };
        queue<Node> q;
        set<string> seen;
        q.push({ start, { start } });
        seen.insert(startSymbol + " ");

        while (!q.empty()) 
        {
            Node cur = q.front(); q.pop();

            string s;
            for (auto &sym : cur.form) s += sym;
            if (s == target) 
            {
                vector<string> deriv;
                for (auto &f : cur.path) {
                    string tmp;
                    for (auto &sym : f) tmp += sym;
                    deriv.push_back(tmp);
                }
                return deriv;
            }

            for (int i = 0; i < (int)cur.form.size(); ++i) 
            {
                string sym = cur.form[i];
                if (rules.count(sym)) 
                {
                    for (auto &alt : rules[sym].rhs) 
                    {
                        Form next;
                        next.insert(next.end(), cur.form.begin(), cur.form.begin() + i);

                        Form tok = tokenize(alt);
                        next.insert(next.end(), tok.begin(), tok.end());

                        next.insert(next.end(), cur.form.begin() + i + 1, cur.form.end());
                        
                        string key;
                        for (auto &x : next) key += x + " ";
                        if (seen.insert(key).second) 
                        {
                            auto newPath = cur.path;
                            newPath.push_back(next);
                            q.push({ next, newPath });
                        }
                    }
                    break;
                }
            }
        }   
        return {};
    }

    vector<string> deriveRightmost(const string& input) 
    {
        using Form = vector<string>;
        struct Node { Form form; vector<Form> path; };
        auto tokenize = [&](const string &alt) {
            Form t;
            for (char c: alt) t.push_back(string(1, c));
            return t;
        };
        string target = input;
        Form start = { startSymbol };
        queue<Node> q;
        set<string> seen;
        q.push({ start, { start } });

        string initKey;
        for (auto &x: start) initKey += x + " ";
        seen.insert(initKey);

        while (!q.empty()) {
            Node cur = q.front(); q.pop();

            string s;
            for (auto &sym : cur.form) s += sym;
            if (s == target) {
                vector<string> deriv;
                for (auto &f : cur.path) {
                    string tmp;
                    for (auto &sym : f) tmp += sym;
                    deriv.push_back(tmp);
                }
                return deriv;
            }

            for (int i = (int)cur.form.size() - 1; i >= 0; --i) {
                string sym = cur.form[i];
                if (rules.count(sym)) {

                    for (auto &alt : rules[sym].rhs) {
                        Form next;

                        next.insert(next.end(), cur.form.begin(), cur.form.begin() + i);
 
                        Form tok = tokenize(alt);
                        next.insert(next.end(), tok.begin(), tok.end());

                        next.insert(next.end(), cur.form.begin() + i + 1, cur.form.end());

                        string key;
                        for (auto &x : next) key += x + " ";
                        if (seen.insert(key).second) {
                            auto newPath = cur.path;
                            newPath.push_back(next);
                            q.push({ next, newPath });
                        }
                    }
                    break;
                }
            }
        }
        return {};
    }

private:
    string derive(vector<string>& symbols, map<string,Production>& checked, int depth)
    {
        //srand(time(NULL));
        int E_counter[3] = {0};
        std::random_device rd;
        if (depth < 0)
        {   
            for (string& sym : symbols)
            {
                if (isNonTerminal(sym)) return "E"; // failed derivation
            }
            string result;
            for (string& sym : symbols) result += sym;
            return result; // case: To be Cecked;
        }

        int flag = 1;
        vector<string> toDerive;
        string result;
        for(string& sys: symbols)
        {
            if(isNonTerminal(sys)) 
            { 
                flag = 0;
                depth--;
                toDerive.push_back(sys);
            }
        }

        if(flag == 1) // case where no non-terminals in symbols
        {
            for(string& sys: symbols)
            {
                result += sys;
            }
            return result;
        }

        // Try to build the result symbol by symbol
        string test;
        
        for(string& sym : toDerive)
        {
            sos:
            if(E_counter[0] >= 10 || E_counter[1] >= 10 || E_counter[2] >= 10)
            {
                return "E";
            }
            test = rules[sym].rhs[rd() % rules[sym].rhs.size()];
            if(test == "" && depth > 0)
            {
                //cout << "helo 1 ";
                E_counter[0]++;
                goto sos;
            }
        
            //check if test is present in checked.
            auto it = find(checked[sym].rhs.begin(), checked[sym].rhs.end(), test);
            if (it != checked[sym].rhs.end()) 
            {
                // test(Production rule is in checked)
                //cout << "helo 2 ";
                E_counter[1]++;
                goto sos;
            }

            vector<string> NewSymobls;
            for(int i=0;i<test.length();i++)
            {
                NewSymobls.push_back(string(1,test[i]));
            }
            string str = derive(NewSymobls, checked, depth);
            if(str == "E")
            {
                E_counter[2]++;
                checked[sym].lhs = sym;
                checked[sym].rhs.push_back(test);
                goto sos;
            }
            else
            {
                //cout << "it is: " << str << endl; 
                replaceStringWithVector(symbols, sym, str);
                continue;
            }
        }

        for (string& sym : symbols) result += sym;
        return result;
    }

    bool isNonTerminal(const string& sym) 
    {
        return rules.find(sym) != rules.end();
    }

    vector<string> tokenize(const string &alt) 
    {
        vector<string> toks;
        for (char c: alt) toks.push_back(string(1, c));
        return toks;
    }

    friend ostream& operator<<(ostream& os, const CFG& p);
    friend void writeGrammarArrayToFile(const string& filename);
    friend void readGrammarArrayFromFile(const string& filename);
};

ostream& operator<<(ostream& os, const CFG& p) 
{
    for(const auto& [symbol, prod_rule] : p.rules)
    {
        if(symbol == "S'")
        {
            continue;
        }
        cout << "Non-Terminal : " << symbol << endl;
        for(int i=0;i<prod_rule.rhs.size(); i++)
        {
            // string str = "";
            // for(int j=0;j<prod_rule.rhs[i].size();j++)
            // {
            //     str += prod_rule.rhs[i][j];
            // }
            cout << "Rule: " << prod_rule.rhs[i] << endl;
        }
    }
    return os;
}

vector<CFG> cfg_arr;
set<int, greater<int>> leaderboard[3]; // 0=easy, 1=m, 2=h

void writeGrammarArrayToFile(const string& filename) 
{
    ofstream outFile(filename);

    for (const auto& grammar : cfg_arr) {
        outFile << "START " << grammar.startSymbol << "\n";
        outFile << "RULES " << grammar.rules.size() << "\n";
        for (const auto& [key, prod] : grammar.rules) 
        {
            outFile << key << " -> " << prod.lhs;
            for (const auto& sym : prod.rhs) 
            {
                if(sym == "")
                {
                    outFile << " empty";
                }
                else
                {
                    outFile << " " << sym;
                }   
            }
            outFile << "\n";
        }
        outFile << "END\n";
    }

    outFile.close();
}

void readGrammarArrayFromFile(const string& filename) 
{
    cfg_arr.clear();

    ifstream inFile(filename);
    string line;

    while (getline(inFile, line)) {
        if (line.substr(0, 6) == "START ") {
            CFG g("S");
            g.startSymbol = line.substr(6);

            getline(inFile, line); // RULES n
            int ruleCount = stoi(line.substr(6));

            for (int i = 0; i < ruleCount; ++i) {
                getline(inFile, line);
                size_t arrowPos = line.find("->");
                string key = line.substr(0, arrowPos - 1);
                string rest = line.substr(arrowPos + 3);

                istringstream ss(rest);
                Production p;
                ss >> p.lhs;

                string sym;
                while (ss >> sym) {
                    if (sym == "empty") {
                        p.rhs.push_back(""); // Interpret "empty" as ""
                    } else {
                        p.rhs.push_back(sym);
                    }
                }

                g.rules[key] = p;
            }

            getline(inFile, line); // END
            cfg_arr.push_back(g);
        }
    }

    inFile.close();
    return;
}

void writeScoreFromFile()
{
    ofstream outFile("Scoreboard.txt");

    for(int i=0; i<3;i++)
    {
       // outFile << "START\n";
        for(int item : leaderboard[i])
        {
            outFile << item << " ";
        }
        outFile << "\n";
       // outFile << "END\n";
    }
    outFile.close();
    return;
}

void readScoreFromFile()
{
    ifstream inFile("Scoreboard.txt");
    string line;
    int i = 0;

    while(getline(inFile, line) && i < 3)
    {
        istringstream ss(line);
        int item;
        while(ss >> item)
        {
            leaderboard[i].insert(item);
        }
        i++;
    }

    inFile.close();
}

void Add_CFGs()
{
    string difficulty;
    cout << "Select New CFG difficuly(easy,medium,hard) : ";
    cin >> difficulty;
    if(difficulty == "easy")
    {
        difficulty = "easy_cfgs.txt";
        readGrammarArrayFromFile("easy_cfgs.txt");
    }
    else if(difficulty == "medium")
    {
        difficulty = "medium_cfgs.txt";
        readGrammarArrayFromFile("medium_cfgs.txt");
    }
    else if(difficulty == "hard")
    {
        difficulty = "hard_cfgs.txt";
        readGrammarArrayFromFile("hard_cfgs.txt");
    }
    else
    {
        cout <<"Invalid Difficulty Option." << endl;
        return;
    }

    string init;
    int counter = 0;
    vector<string> prod_rule;
    CFG cfg("S");

    cout << "Add Rules: " << endl;
    while(1)
    {
        prod_rule.clear();
        cout << "Enter Non-Terminal : ";
        cin >> init;
        if(init == "stop")
        {
            break;
        }
        while(1)
        {
            string str;
            cout << "Product rule counter(empty for \"\") " << counter +1 << " : ";
            cin >> str;
            if(str == "next")
            {
                cfg.addRule(init, prod_rule);
                break;
            }
            if(str == "empty")
            {
                str = "";
            }
            prod_rule.push_back(str);
            counter++;
        }
    }

    cfg_arr.push_back(cfg);

    writeGrammarArrayToFile(difficulty);
   
    return;
}

void View_CFGs()
{
    string difficulty;
    cout << "Select CFG difficuly to view(easy,medium,hard) : ";
    cin >> difficulty;
    if(difficulty == "easy")
    {
        difficulty = "easy_cfgs.txt";
    }
    else if(difficulty == "medium")
    {
        difficulty = "medium_cfgs.txt";
    }
    else if(difficulty == "hard")
    {
        difficulty = "hard_cfgs.txt";
    }
    else
    {
        cout <<"Invalid Difficulty Option." << endl;
        return;
    }
    readGrammarArrayFromFile(difficulty);
    cout << endl;
    for(int i=0;i<cfg_arr.size();i++)
    {
        cout << i+1 << ". " << cfg_arr[i] << endl;
    }

    int opt;
    cout << "Enter Index of CFG to delete(0 to exit) : ";
    cin >> opt;

    if(opt == 0)
    {
        return;
    }
    else if(opt <= cfg_arr.size())
    {
        cfg_arr.erase(cfg_arr.begin() + opt-1);
        writeGrammarArrayToFile(difficulty);
    }
    else
    {
        cout << "Invalid Option. " << endl;
        return;
    }
    
}

void Admin_fun()
{
    int opt;

    sos:
    cout << "1. Add CFGs" << endl;
    cout << "2. View/Remove CFGs" << endl;
    cout << "3. Exit" << endl;
    cout << "Choose : ";

    cin >> opt;

    switch (opt)
    {
    case 1:
        Add_CFGs();
        goto sos;
        break;
    case 2:
        View_CFGs();
        goto sos;
        break;
    case 3:
        return;
        break;
    default:
        cout << "Try Again." << endl;
        goto sos;
        break;
    }
}

bool type1()
{
    int try_counter = 0;
    srand(time(NULL));
    int it = rand()%cfg_arr.size();
    
    cout << "Select the invalid string from the followiing CFG :\n" << cfg_arr[it] << endl;
    string options[4];
    for(int i=0;i<3;i++)
    {
        options[i] = cfg_arr[it].generateString(6);
    }

    try_again:
    std::random_device rd;
    int it2 = rd() % cfg_arr.size();
    //int it2 = rand()%cfg_arr.size();
    if(it2 == it)
    {
        //cout << "we are trying again " << endl;
        try_counter++;
        goto try_again;
    }

    options[3] = cfg_arr[it2].generateString(6);
    if(cfg_arr[it].isValidString(options[3]))
    {
        //cout << "we are trying again " << endl;
        try_counter++;
        goto try_again;
    }
    cout << options[3] << " ANS here " << endl;
    string ans = options[3];

    unsigned seed = chrono::system_clock::now().time_since_epoch().count();
    shuffle(options, options + 4, default_random_engine(seed));

    for(int i=0;i<4;i++)
    {
        cout << i+1 << ". " << options[i] << endl;
    }
    int opt;
    cout << "Choose: " ;
    cin >> opt; 

    if(options[opt-1] == ans)
    {
        cout << "Correct Answer!!! " << endl;
        return true;
    }
    else
    {
        cout << "Better Luck Next Time!!!" << endl;
        return false;
    }
}

bool type2()
{
    int try_counter = 0;
    srand(time(NULL));
    int it = rand()%cfg_arr.size();
    
    cout << "Select the valid string from the followiing CFG :\n" << cfg_arr[it] << endl;

    string options[4];
    options[0] = cfg_arr[it].generateString(6);

    cout << options[0] << " ANS here " << endl;
    string ans = options[0];

    for(int j=1;j<4;j++)
    {
        try_again:
        std::random_device rd;
        int it2 = rd() % cfg_arr.size();
        //int it2 = rand()%cfg_arr.size();
        if(it2 == it)
        {
            //cout << "we are trying again " << endl;
            try_counter++;
            goto try_again;
        }

        options[j] = cfg_arr[it2].generateString(6);
        if(cfg_arr[it].isValidString(options[j])) // try again if the give string is 'valid'. we want invalid strings
        {
            //cout << "we are trying again " << endl;
            try_counter++;
            goto try_again;
        }
    }
    
    unsigned seed = chrono::system_clock::now().time_since_epoch().count();
    shuffle(options, options + 4, default_random_engine(seed));

    for(int i=0;i<4;i++)
    {
        cout << i+1 << ". " << options[i] << endl;
    }
    int opt;
    cout << "Choose: " ;
    cin >> opt; 

    if(options[opt-1] == ans)
    {
        cout << "Correct Answer!!! " << endl;
        return true;
    }
    else
    {
        cout << "Better Luck Next Time!!!" << endl;
        return false;
    }
}

bool type3()
{
    std::random_device rd;
    int it = rd() % cfg_arr.size();
    string str = cfg_arr[it].generateString(6);
    cout << "Derive the following string \'" << str << "\' using the given CFG\n Use left Expansion method" << endl;
    cout << cfg_arr[it] << endl;

    vector<string> mod = cfg_arr[it].deriveLeftmost(str);
    vector<string> ans;
    string opt;
    cout << "Enter 'done' when final answer reached" << endl;
    while(1)
    {
        cin >> opt;
        if(opt == "done")
        {
            break;
        }
        ans.push_back(opt);
    }
    
    if(ans == mod)
    {
        cout << "Correct Answer!!" << endl;
        return true;
    }
    else
    {
        cout << "Better Luck Next Time!" << endl;
        return false;
    }
}

bool type4()
{
    std::random_device rd;
    int it = rd() % cfg_arr.size();
    string str = cfg_arr[it].generateString(6);
    cout << "Derive the following string \'" << str << "\' using the given CFG\n Use Right Expansion method" << endl;
    cout << cfg_arr[it] << endl;

    vector<string> mod = cfg_arr[it].deriveRightmost(str);
    vector<string> ans;
    string opt;
    cout << "Enter 'done' when final answer reached" << endl;
    while(1)
    {
        cin >> opt;
        if(opt == "done")
        {
            break;
        }
        ans.push_back(opt);
    }
    
    if(ans == mod)
    {
        cout << "Correct Answer!!" << endl;
        return true;
    }
    else
    {
        cout << "Better Luck Next Time!" << endl;
        return false;
    }
}

void Quiz()
{
    string difficulty;
    int difficulty_rank;
    cout << "Select Quiz difficuly(easy,medium,hard) : ";
    cin >> difficulty;
    if(difficulty == "easy")
    {
        difficulty = "easy_cfgs.txt";
        difficulty_rank = 0;
        readGrammarArrayFromFile("easy_cfgs.txt");
    }
    else if(difficulty == "medium")
    {
        difficulty = "medium_cfgs.txt";
        difficulty_rank = 1;
        readGrammarArrayFromFile("medium_cfgs.txt");
    }
    else if(difficulty == "hard")
    {
        difficulty = "hard_cfgs.txt";
        difficulty_rank = 2;
        readGrammarArrayFromFile("hard_cfgs.txt");
    }
    else
    {
        cout <<"Invalid Difficulty Option." << endl;
        return;
    }

    int streak=0, points=0;
    bool ret;
    std::random_device rd;
    for(int i=0; i<10;i++)
    {
        int it = rd()%5;
        switch(it)
        {
            case 1:
                ret = type1(); // guess invalid string
                cout << endl;
                break;
            case 2:
                ret = type2(); // guess invalid string
                cout << endl;
                break;
            case 3:
                ret = type3(); // guess derivation
                cout << endl;
                break;
            case 4:
                ret = type4();
                cout << endl;
        }
        if(ret)
        {
            streak++;
            points += 1*streak;
        }
        else
        {
            streak=0;
        }
        continue;
    }
    leaderboard[difficulty_rank].insert(points);
    writeScoreFromFile();
    cout << endl << "You Scored : " << points << endl;
    getchar();
}

void test_fun()
{
    // cout << cfg_arr[1].isValidString("aaabbb") << endl;
    // cout << cfg_arr[0].isValidString("aaacccbbdd") << endl;
    // cout << cfg_arr[0].isValidString("aaacc") << endl;
    // cout << cfg_arr[0].isValidString("aaabbb") << endl;
    // cout << cfg_arr[0].isValidString("aaadd") << endl;
    // cout << cfg_arr[0].isValidString("bbbddd") << endl;

    vector<string> mod = cfg_arr[0].deriveLeftmost(cfg_arr[0].generateString(6));

    for(int i=0;i<mod.size();i++)
    {
        cout << mod[i] << endl;
    }
}

int main() 
{
    srand(time(0));
    int opt;

    readGrammarArrayFromFile("easy_cfgs.txt");
    readScoreFromFile();

    sos:
    cout << "1. Quiz" << endl;
    cout << "2. Admin" << endl;
    cout << "3. Exit" << endl;
    cout << "Choose : " ;

    cin >> opt;

    switch (opt)
    {
        case 1:
            Quiz();
            break;
        case 2:
            Admin_fun();
            goto sos;
            break;
        case 3:
            exit(0);
            break;
        default:
            cout << "Try Again." << endl;
            goto sos;
            break;
    }

    return 0;
}
