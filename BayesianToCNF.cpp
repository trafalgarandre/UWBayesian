#include <iostream>
#include <fstream>
#include <vector>
#include <algorithm>
#include <stack>
#include <unordered_map>
#include <stdio.h>
#include <string.h>
#include <string>
#include <math.h>

using namespace std;

class CNFFormula {
public:
    // CNF form, vector of clauses
    vector<vector<int>> formula;
    CNFFormula() {
        formula.clear();
    }

    CNFFormula(vector<vector<int>> f) {
        formula = f;
    }

    int getNumClause() {
        return formula.size();
    }

    void andFormula(CNFFormula f) {
        for (vector<int> vi: f.formula) {
            addClause(vi);
        }
    }

    void addClause(vector<int> clause) {
        formula.push_back(clause);
    }


    void or1Var(int v) {
        if (formula.size() == 0) {
            formula.push_back({v});
        } else {
            for (int i = 0; i < formula.size(); i++) {
                formula[i].push_back(v);
            }
        }
    }

    void and1Var(int v) {
        addClause({v});
    }

    static CNFFormula and1Var(CNFFormula f, int v) {
        CNFFormula* result = new CNFFormula();
        result->andFormula(f);
        result->and1Var(v);
        return *result;
    }

    static CNFFormula or1Var(CNFFormula f, int v) {
        CNFFormula* result = new CNFFormula();
        result->andFormula(f);
        result->or1Var(v);
        return *result;
    }
};

class ChainFormula {
public:
    vector<int> variables;
    vector<bool> operators;

    // 0 is ^ and 1 is V
    CNFFormula toCNFFormula() {
        CNFFormula* result = new CNFFormula;
        result->and1Var(variables[variables.size() - 1]);
        for (int i = variables.size() - 2; i >= 0; i--) {
            if (operators[i] == 0) {
                result->and1Var(variables[i]);
            } else {
                result->or1Var(variables[i]);
            }
        }
        return *result;
    }
};

class ImplyFormula {
public:
    CNFFormula left;
    CNFFormula right;
    ImplyFormula(CNFFormula* _l, CNFFormula* _r) {
        left = *_l;
        right = *_r;
    }

    CNFFormula toCNFFormula() {
        // the left in the format a ^ b ^ c ^ d
        // the right supposes to only have 1 variable
        CNFFormula result;
        for (vector<int> vi: right.formula) {
            vector<int> temp = vi;
            for (vector<int> vi2: left.formula) {
                temp.push_back(-vi2[0]);
            }
            result.addClause(temp);
        }
        return result;
    }
};

class Frac {
public:
    int numerator;
    int denominator;
    int reduce_factor; // use to extend m' -> m, (x V ()) ^ *()
    int seed;
    int length;
    double c;
    ChainFormula chain;
    CNFFormula f;
    Frac(int _numerator, int _denominator) {
        numerator = _numerator;
        reduce_factor = 0;
        denominator = pow(2, ceil(log2(_denominator)));
        c = ((double)denominator) / _denominator;
    }

    void toLowestForm() {
        while (numerator % 2 == 0 && denominator % 2 == 0) {
            numerator /= 2;
            denominator /= 2;
            reduce_factor++;
        }
    }

    void constructChainFormula(int _seed) {
        seed = _seed;
        toLowestForm();
        int num = numerator;
        int den = denominator;
        stack<int> temp_stack;
        num--;
        den--;
        while (num != 0 || den != 0) {
            if (num & 1 == 0) {
                temp_stack.push(false);
            } else {
                temp_stack.push(true);
            }
            num = num >> 1;
            den = den >> 1;
           // _seed++;
        }

        chain.variables.push_back(seed);
        seed++;
        while (!temp_stack.empty()) {
            chain.operators.push_back(temp_stack.top());
            temp_stack.pop();
            chain.variables.push_back(seed);
            seed++;
        }
        // update length - number of variables using seed
    }

    void toCNFFormula() {
        f.andFormula(chain.toCNFFormula());
    }

    // compulsory if reduce_factor != 0
    // (a V b) ^ (-a V b)
    void extendFromReduction() {
        while (reduce_factor != 0) {
            CNFFormula* f1 = new CNFFormula();
            f1->andFormula(CNFFormula::or1Var(f, seed));
            f.andFormula(*f1);
            //f1 = (CNFFormula::or1Var(f, seed));
            //f1.andFormula((CNFFormula::or1Var(f, -seed)));
            //f = f1;
            seed++;
            reduce_factor--;
        }
    }

    void constructCNFFormula(int _seed) {
        constructChainFormula(_seed);
        toCNFFormula();
        extendFromReduction();
    }

    int returnSeed() {
        return seed;
    }

    double getC() {
        return c;
    }
};

class Bayes {
public:
    int num_nodes;
    vector<int> cardinality;
    vector<vector<int>> parent;
    vector<vector<double>> cpt;
    vector<int> cpt_denominator;
    unordered_map<string, int> hmap;
    int seed = 1;
    CNFFormula formula;
    double C = 1;

    void createKB() {
        formula = generateIndicator();
        CNFFormula par = generateParameter();
        formula.andFormula(par);
    }

    CNFFormula generateIndicator() {
        CNFFormula result;
        for (int i = 0; i < num_nodes; i++) {
            vector<int> clause;
            for (int j = 0; j < cardinality[i]; j++) {
                string key = to_string(i) + " " + to_string(j);
                hmap.emplace(key, seed);
                clause.push_back(seed);
                seed++;
            }
            result.addClause(clause);
            vector<int> only1Clause;
            for (int j = 1; j < cardinality[i]; j++) {
                for (int k = 0; k < j; k++) {
                    string key1 = to_string(i) + " " + to_string(j);
                    string key2 = to_string(i) + " " + to_string(k);
                    only1Clause.push_back(-(hmap.at(key1)));
                    only1Clause.push_back(-(hmap.at(key2)));
                    result.addClause(only1Clause);
                }
            }
        }
        return result;
    }

    CNFFormula generateParameter() {
        CNFFormula result;
        for (int i = 0; i < num_nodes; i++) {
            int start_seed = seed;
            int end_seed = 0;
            vector<int> vi = parent[i];
            vi.push_back(i);
            int pos = vi.size() - 1;
            int arr[vi.size()];
            memset(arr, 0, sizeof(arr));
            int index = 0;
            bool getC = false;
            while (pos >= 0) {
                CNFFormula left;
                CNFFormula right;
                for (int j = 0; j < vi.size(); j++) {
                    if (j != vi.size() - 1) {
                        string key = to_string(parent[i][j]) + " " + to_string(arr[j]);
                        left.and1Var(hmap.at(key));
                    } else {
                        string key = to_string(i) + " " + to_string(arr[j]);
                        left.and1Var(hmap.at(key));
                    }
                }
                Frac frac((int)(cpt[i][index] * cpt_denominator[i]), cpt_denominator[i]);
                //Frac frac((int)(cpt[i][index] * 10), 4);
                if (!getC) {
                    getC = true;
                    C *= frac.getC();
                }
                frac.constructCNFFormula(start_seed);
                int temp_seed = frac.returnSeed();
                if (temp_seed > end_seed) end_seed = temp_seed;
                ImplyFormula imply(&left, &frac.f);
                result.andFormula(imply.toCNFFormula());
                bool step = false;
                while (arr[pos] == cardinality[vi[pos]] - 1) {
                    pos--;
                    step = true;
                }
                index++;
                if (pos >= 0 && !step) {
                    if (!step) {
                        arr[pos]++;
                    } else {
                        for (int j = pos + 1; j < vi.size(); j++) {
                            arr[j] = 0;
                        }
                    }
                }
            }
            seed = end_seed;
        }
        return result;
    }

    double getC() {
        return C;
    }

    void addEvid(int var, int val) {
        formula.addClause({hmap.at(to_string(var) + " " + to_string(val))});
    }
};

Bayes bayes;
//const Frac C = Frac(16777216, 10000000);

int main()
{
    ofstream cnfFile, CFile;
    ifstream bayesFile, evidFile;
    bayesFile.open("in2.txt");
    cnfFile.open ("cnf.txt");
    CFile.open("c.txt");
    evidFile.open("evid.txt");
    //freopen("in2.txt", "r", stdin);
    //Start inputing
    string type;
    bayesFile >> type;
    int ignore;
    //cout << type << endl;
    if (type != "BAYES") {
        throw "Not Bayes";
    }

    bayesFile >> bayes.num_nodes;

    for (int i = 0; i < bayes.num_nodes; i++) {
        int temp;
        bayesFile >> temp;
        bayes.cardinality.push_back(temp);
        bayes.parent.push_back({});
        bayes.cpt.push_back({});
    }

    bayesFile >> ignore;

    for (int i = 0; i < bayes.num_nodes; i++) {
        int cpt_nums;
        bayesFile >> cpt_nums;
        for (int j = 0; j < cpt_nums - 1; j++) {
            int temp;
            bayesFile >> temp;
            bayes.parent[i].push_back(temp);
        }
        bayesFile >> ignore;
    }

    for (int i = 0; i < bayes.num_nodes; i++) {
        int num_network_params;
        bayesFile >> num_network_params;
        int den_num = 0;
        for (int j = 0; j < num_network_params; j++) {
            string temp_str;
            double temp;
            bayesFile >> temp_str;
            if (!temp_str.empty()) {
                temp = stod(temp_str);
                bayes.cpt[i].push_back(temp);
                int temp_den_num = temp_str.length() - temp_str.find('.');
                den_num = max(den_num, temp_den_num);
            }
        }
        int den_value = 1;
        for (int i = 0; i < den_num; i++) {
            den_value *= 10;
        }
        bayes.cpt_denominator.push_back(den_value);
    }
    // End inputing

    bayes.createKB();

    int num_var;
    evidFile >> num_var;
    for (int i = 0; i < num_var; i++) {
        int var_num, var_val;
        evidFile >> var_num >> var_val;
        bayes.addEvid(var_num, var_val);
    }

    cnfFile << "p cnf " << bayes.seed << " " << bayes.formula.getNumClause() << "\n";
    for (vector<int> vi: bayes.formula.formula) {
        for (int i: vi) {
            cnfFile << i << " ";
        }
        cnfFile << "0\n";
    }

    CFile << bayes.C;
    cnfFile.close();
    CFile.close();
    bayesFile.close();
    return 0;
}
