#include <iostream>
#include <stdlib.h>
#include <algorithm>
#include <vector>
#include <cmath>
#include <cstdio>
#include <queue>

using namespace std;

#define UNDEF -1
#define TRUE 1
#define FALSE 0

struct lit_in {
    vector<int> positive;
    vector<int> negative;
};

struct comp {
    bool operator() (const pair<int,int> p1, const pair<int,int> p2) {
        return p1.second <= p2.second;
    }
};

uint numVars;
uint numClauses;
uint btrack = 0;
uint decisions = 0;
vector<vector<int> > clauses;
vector<int> model;
vector<int> modelStack;
vector<lit_in> mem;
vector<int> scores;
priority_queue<pair<int,int>, vector<pair<int,int> >, comp> ranking;
uint indexOfNextLitToPropagate;
uint decisionLevel;
vector<bool> used;


void setLiteralToTrue(int lit){
    modelStack.push_back(lit);
    if (lit > 0) model[lit] = TRUE;
    else model[-lit] = FALSE;
}

void literalElimination() {
    for(int i = 0; i < mem.size(); ++i) {
        if(mem[i].positive.empty()) {
            setLiteralToTrue(-(i+1));
            modelStack.push_back(0);
        }
        else if(mem[i].negative.empty()) {
            setLiteralToTrue(i+1);
            modelStack.push_back(0);
        }
    }
}

void readClauses(){
    // Skip comments
    char c = cin.get();
    while (c == 'c') {
        while (c != '\n') c = cin.get();
        c = cin.get();
    }  
    // Read "cnf numVars numClauses"
    string aux;
    cin >> aux >> numVars >> numClauses;
    clauses.resize(numClauses);
    
    mem.resize(numVars);
    scores.resize(numVars);
    // Read clauses
    for (uint i = 0; i < numClauses; ++i) {
        int lit;
        while (cin >> lit and lit != 0) {
            clauses[i].push_back(lit);
            
            if (lit < 0) {
                mem[abs(lit)-1].negative.push_back(i);
            }
            else {
                mem[lit-1].positive.push_back(i);
            }
            ++scores[lit-1];
        }
    }
    
    for(int i = 0; i < numVars; ++i) ranking.push(make_pair(i+1,scores[i]));
    
    model.resize(numVars+1,UNDEF);
    literalElimination();
}

int currentValueInModel(int lit){
    if (lit >= 0) return model[lit];
    else {
        if (model[-lit] == UNDEF) return UNDEF;
        else return 1 - model[-lit];
    }
}


bool propagateGivesConflict ( ) {
    while (indexOfNextLitToPropagate < modelStack.size()) {
        int lit = modelStack[indexOfNextLitToPropagate];
        ++indexOfNextLitToPropagate;
        if (lit < 0) {
            lit = abs(lit);
            for (uint i = 0; i < mem[lit-1].positive.size(); ++i) {
                bool someLitTrue = false;
                int numUndefs = 0;
                int lastLitUndef = 0;
                for (uint k = 0; not someLitTrue and k < clauses[mem[lit-1].positive[i]].size(); ++k){
                    int val = currentValueInModel(clauses[mem[lit-1].positive[i]][k]);
                    if (val == TRUE) someLitTrue = true;
                    else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[mem[lit-1].positive[i]][k]; }
                }
                if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
                else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);	
            }    
        }
        else {
            for (uint i = 0; i < mem[lit-1].negative.size(); ++i) {
                bool someLitTrue = false;
                int numUndefs = 0;
                int lastLitUndef = 0;
                for (uint k = 0; not someLitTrue and k < clauses[mem[lit-1].negative[i]].size(); ++k){
                    int val = currentValueInModel(clauses[mem[lit-1].negative[i]][k]);
                    if (val == TRUE) someLitTrue = true;
                    else if (val == UNDEF){ ++numUndefs; lastLitUndef = clauses[mem[lit-1].negative[i]][k]; }
                }
                if (not someLitTrue and numUndefs == 0) return true; // conflict! all lits false
                else if (not someLitTrue and numUndefs == 1) setLiteralToTrue(lastLitUndef);	
            }    
        }
    }
    return false;
}


void backtrack(){
    ++btrack;
    uint i = modelStack.size() -1;
    int lit = 0;
    while (modelStack[i] != 0){ // 0 is the DL mark
        lit = modelStack[i];
        model[abs(lit)] = UNDEF;
        modelStack.pop_back();
        --i;
    }
    // at this point, lit is the last decision
    modelStack.pop_back(); // remove the DL mark
    --decisionLevel;
    indexOfNextLitToPropagate = modelStack.size();
    setLiteralToTrue(-lit);  // reverse last decision
}


// Heuristic for finding the next decision literal:
<<<<<<< HEAD
int getNextDecisionLiteral() {
    while(ranking.top())
=======
int getNextDecisionLiteral(){
    ++decisions;
    pair<int,int> max = make_pair(0,0);
    for(int i = 0; i < mem.size(); ++i) {
        if (model[i+1] == UNDEF) {
            int contPos = 0;
            for(int j = 0; j < mem[i].positive.size(); ++j) {
                if(not used[j]) {
                    bool someTrue = false;
                    for(int k = 0; not someTrue and k < clauses[mem[i].positive[j]].size(); ++k)
                        someTrue = (currentValueInModel(clauses[mem[i].positive[j]][k]) == TRUE);
                    used[j] = true;
                    if (not someTrue) ++contPos;
                }
            }
            int contNeg = 0;
            for(int j = 0; j < mem[i].negative.size(); ++j) {
                if(not used[j]) {
                    bool someTrue = false;
                    for(int k = 0; not someTrue and k < clauses[mem[i].negative[j]].size(); ++k)
                        someTrue = (currentValueInModel(clauses[mem[i].negative[j]][k]) == TRUE);
                    used[j] = true;
                    if (not someTrue) ++contNeg;
                }
            }
            if(contPos > max.second) {
                max.first = i+1;
                max.second = contPos;
            }
            if(contNeg > max.second) {
                max.first = -(i+1);
                max.second = contNeg;
            }
        }
    }
    return max.first;
>>>>>>> 03f534ecc688e3b20f978d6223f357c65c06bbc1
}

void checkmodel(){
    for (int i = 0; i < numClauses; ++i){
        bool someTrue = false;
        for (int j = 0; not someTrue and j < clauses[i].size(); ++j)
            someTrue = (currentValueInModel(clauses[i][j]) == TRUE);
        if (not someTrue) {
            cout << "Error in model, clause is not satisfied:";
            for (int j = 0; j < clauses[i].size(); ++j) cout << clauses[i][j] << " ";
            cout << endl;
            exit(1);
        }
    }  
}

int main(int argc, char *argv[]){
    
    if(argc > 1) freopen(argv[1],"r",stdin);
    else exit(0);
    
    readClauses(); // reads numVars, numClauses and clauses
<<<<<<< HEAD
=======
    used.resize(numClauses,false);
>>>>>>> 03f534ecc688e3b20f978d6223f357c65c06bbc1
    indexOfNextLitToPropagate = modelStack.size();  
    decisionLevel = 0;
    
    // Take care of initial unit clauses, if any
    for (uint i = 0; i < numClauses; ++i)
        if (clauses[i].size() == 1) {
            int lit = clauses[i][0];
            int val = currentValueInModel(lit);
            if (val == FALSE) {
                cout << "UNSATISFIABLE" << endl << "Backtracks: "<< btrack << endl << "Decisions: "<< decisions << endl; 
                return 10;
            }
            else if (val == UNDEF) setLiteralToTrue(lit);
        }
        // DPLL algorithm
        while (true) {
            while (propagateGivesConflict()) {
                if ( decisionLevel == 0) { 
                    cout << "UNSATISFIABLE" << endl << "Backtracks: " << btrack << endl << "Decisions: "<< decisions << endl; 
                    return 10; 
                }
                backtrack();
            }
            int decisionLit = getNextDecisionLiteral();
            if (decisionLit == 0) { 
                checkmodel(); 
                cout << "SATISFIABLE" << endl << "Backtracks: " << btrack << endl << "Decisions: "<< decisions << endl; 
                return 20; 
            }
            // start new decision level:
            modelStack.push_back(0);  // push mark indicating new DL
            used.resize(numClauses,false);
            ++indexOfNextLitToPropagate;
            ++decisionLevel;
            setLiteralToTrue(decisionLit);    // now push decisionLit on top of the mark
        }
<<<<<<< HEAD
}
=======
}  
>>>>>>> 03f534ecc688e3b20f978d6223f357c65c06bbc1