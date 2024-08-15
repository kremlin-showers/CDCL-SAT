// Implementing a CDCL SAT solver
#include <algorithm>
#include <cmath>
#include <iostream>
#include <random>
#include <vector>

using namespace std;

// enum for the return values
enum RetVal {
  sat_c,   // the formula has been satisfied
  unsat_c, // the formula has been unsatisfied
  nor_c       // the formula is unresolved so far
};

// Main class
class CDCL_solver {
private:
  // Vector assignments 1, -1 and 0 for assigned, unassigned and assigned false
  // resepectuvely
  vector<int> literals;

  // Storing the clauses
  vector<vector<int>> literal_list_per_clause;

  // Storing freq
  vector<int> literal_frequency;

  // Difference in no of positive and negative instances of literasl
  vector<int> literal_polarity;

  // Original frequencies (backup to restore when variables are unassigned)
  vector<int> original_var_freq;
  int var_count;
  int clause_count;
  int kappa_antecedent;

  // Stores decision level
  vector<int> literal_decision_level;

  // Stores antecedent
  vector<int> literal_antecedent;
  int assigned_literal_count;
  bool already_unsatisfied; // Initial check for empty clauses

  int pick_counter; // the number of times we have chosen a variable freely
                    // based on frequency
                    // For random generation stuff
  random_device random_generator;
  mt19937 generator;

  // Functions for unit prpogation assignemtns and unassignements
  int unit_propagate(int);
  void assign_literal(int, int, int);
  void unassign_literal(int);

  int literal_to_variable_index(int);
  int conflict_analysis_and_backtrack(
      int); // Backtrackign logic the heart of this solver
  vector<int> &resolve(vector<int> &,
                       int);     // to resolve two clauses and get the result
  int pick_branching_variable(); // next assignment
  bool all_variables_assigned(); // Check if everything is assigned
  void show_result(int);         // DOne!!

public:
  CDCL_solver() : generator(random_generator()) {}
  void initialize(); // Initialize all the vectors properly
  int CDCL(); // to perform the CDCL algorithm and return the appropriate result
              // state
  void solve(); // to solve the problem and display the result
};

void CDCL_solver::initialize() {
  char c;
  string s;

  while (true) {
    cin >> c;
    if (c == 'c') // if comment
    {
      getline(cin, s); // ignore
    } else             // else, if would be a p
    {
      cin >> s; // this would be cnf
      break;
    }
  }
  cin >> var_count;
  cin >> clause_count;
  // Initial values
  assigned_literal_count = 0;
  kappa_antecedent = -1;
  pick_counter = 0;
  already_unsatisfied = false;

  // Proper vector sizes
  literals.clear();
  literals.resize(var_count, -1);
  literal_frequency.clear();
  literal_frequency.resize(var_count, 0);
  literal_polarity.clear();
  literal_polarity.resize(var_count, 0);
  literal_list_per_clause.clear();
  literal_list_per_clause.resize(clause_count);
  literal_antecedent.clear();
  literal_antecedent.resize(var_count, -1);
  literal_decision_level.clear();
  literal_decision_level.resize(var_count, -1);

  int literal;
  int literal_count_in_clause = 0;
  // iterate over the clauses
  for (int i = 0; i < clause_count; i++) {
    literal_count_in_clause = 0;
    while (true) // while the ith clause gets more literals
    {
      cin >> literal;
      if (literal > 0) // if the variable has positive polarity
      {
        literal_list_per_clause[i].push_back(literal); // store it
        // increment frequency and polarity of the literal
        literal_frequency[literal - 1]++;
        literal_polarity[literal - 1]++;
      } else if (literal < 0) // if the variable has negative polarity
      {
        literal_list_per_clause[i].push_back(literal); // store it
        // increment frequency and decrement polarity of the literal
        literal_frequency[-1 - literal]++;
        literal_polarity[-1 - literal]--;
      } else {
        if (literal_count_in_clause == 0) // if any clause is empty, we can stop
        {
          already_unsatisfied = true;
        }
        break; // read 0, so move to next clause
      }
      literal_count_in_clause++;
    }
  }
  original_var_freq =
      literal_frequency; // backup for restoring when backtracking
}

// CDCL function
int CDCL_solver::CDCL() {
  // init
  int decision_level = 0;
  // If the given formula is already unsatisfiable
  if (already_unsatisfied)

  {
    return RetVal::unsat_c;
  }
  // Initial propogation
  int unit_propagate_result = unit_propagate(decision_level);
  if (unit_propagate_result == RetVal::unsat_c) {
    return unit_propagate_result;
  }
  while (!all_variables_assigned()) {
    int picked_variable = pick_branching_variable(); // pick next free guy
    decision_level++;
    // Assign the picked variable at the current decision level
    assign_literal(picked_variable, decision_level, -1);
    // Unit propogate and backtrack if needed
    while (true) {
      unit_propagate_result = unit_propagate(decision_level);
      if (unit_propagate_result == RetVal::unsat_c) {
        // if the conflict was at the top level, the formula is unsatisfiable
        if (decision_level == 0) {
          return unit_propagate_result;
        }
        /*
         * if not, perform the conflict analysis, learn clauses, and backtrack
         * to a previous decision level
         */
        decision_level = conflict_analysis_and_backtrack(decision_level);
      } else
      // Here we just need to move to the next free assignment
      {
        break;
      }
    }
  }
  // If we ever reach here it means that all assignments are done and function
  // is actually SAT
  return RetVal::sat_c;
}

// Unit propo
int CDCL_solver::unit_propagate(int decision_level) {
  bool unit_clause_found =
      false; // if a unit clause has been found, false and unset literasls in it
  int false_count = 0;
  int unset_count = 0;
  int literal_index;
  bool satisfied_flag = false;
  int last_unset_literal = -1; // index of an unset literal
  do {
    unit_clause_found = false;
    // iterate over all clauses if no unit clause has been found so far
    for (int i = 0; i < literal_list_per_clause.size() && !unit_clause_found;
         i++) {
      false_count = 0;
      unset_count = 0;
      satisfied_flag = false;
      // iterate over all literals
      for (int j = 0; j < literal_list_per_clause[i].size(); j++) {
        // get the vector index of the literal
        literal_index =
            literal_to_variable_index(literal_list_per_clause[i][j]);
        if (literals[literal_index] == -1) // if unassigned
        {
          unset_count++;
          last_unset_literal = j; // store the index, may be needed later
        } else if ((literals[literal_index] == 0 &&
                    literal_list_per_clause[i][j] > 0) ||
                   (literals[literal_index] == 1 &&
                    literal_list_per_clause[i][j] <
                        0)) // if false in the clause
        {
          false_count++;
        } else // if true in the clause, so the clause is satisfied
        {
          satisfied_flag = true;
          break;
        }
      }
      if (satisfied_flag) // if the clause is satisfied, move to the next
      {
        continue;
      }
      // if exactly one literal is unset, this clause is unit
      if (unset_count == 1) {
        // assign the unset literal at this decision level and this clause i as
        // the antecedent
        assign_literal(literal_list_per_clause[i][last_unset_literal],
                       decision_level, i);
        unit_clause_found =
            true; // we have found a unit clause, so restart iteratin
        break;
      }
      // if the clause is unsatisfied
      else if (false_count == literal_list_per_clause[i].size()) {
        // unsatisfied clause
        kappa_antecedent =
            i; // set the antecedent of kappa to this clause
               // Return unsatisfied as we found unsatisfied conflict clause
        return RetVal::unsat_c; // return a conflict status
      }
    }
  } while (unit_clause_found); // if a unit clause was found, we restart
                               // iterating over the clauses
  kappa_antecedent = -1;
  // Otherwise return normally
  return RetVal::nor_c; // return normally
}

// Assigns antecedent and value to the literal
void CDCL_solver::assign_literal(int variable, int decision_level,
                                   int antecedent) {
  int literal = literal_to_variable_index(variable);
  int value = (variable > 0) ? 1 : 0;
  literals[literal] = value;
  literal_decision_level[literal] = decision_level;
  literal_antecedent[literal] = antecedent;
  literal_frequency[literal] = -1;
  assigned_literal_count++;
}

// Unassigning a literal and handling all the values
void CDCL_solver::unassign_literal(int literal_index) {
  literals[literal_index] = -1;
  literal_decision_level[literal_index] = -1;
  literal_antecedent[literal_index] = -1;
  literal_frequency[literal_index] = original_var_freq[literal_index];
  assigned_literal_count--;
}

// Nice function to convert literal to variable index
int CDCL_solver::literal_to_variable_index(int variable) {
  return (variable > 0) ? variable - 1 : -variable - 1;
}

// Conflict analysis and bakctracking. The fun stuffj
int CDCL_solver::conflict_analysis_and_backtrack(int decision_level) {
  vector<int> learnt_clause = literal_list_per_clause[kappa_antecedent];
  int conflict_decision_level = decision_level;
  int this_level_count = 0;
  int resolver_literal;
  int literal;
  do {
    this_level_count = 0;
    // iterate over all literals
    for (int i = 0; i < learnt_clause.size(); i++) {
      literal = literal_to_variable_index(learnt_clause[i]); // get the index
      // if a literal at the same decision level has been found
      if (literal_decision_level[literal] == conflict_decision_level) {
        this_level_count++;
      }
      if (literal_decision_level[literal] == conflict_decision_level &&
          literal_antecedent[literal] != -1) {
        resolver_literal = literal;
      }
    }
    // exactly one literal at the same decision level means we have a UIP
    if (this_level_count == 1) {
      break;
    }
    learnt_clause = resolve(learnt_clause, resolver_literal);
  } while (true);
  literal_list_per_clause.push_back(learnt_clause);
  for (int i = 0; i < learnt_clause.size(); i++) {
    int literal_index = literal_to_variable_index(learnt_clause[i]);
    int update = (learnt_clause[i] > 0) ? 1 : -1;
    literal_polarity[literal_index] += update;
    if (literal_frequency[literal_index] != -1) {
      literal_frequency[literal_index]++;
    }
    original_var_freq[literal_index]++;
  }
  clause_count++;
  int backtracked_decision_level = 0;
  for (int i = 0; i < learnt_clause.size(); i++) {
    int literal_index = literal_to_variable_index(learnt_clause[i]);
    int decision_level_here = literal_decision_level[literal_index];
    if (decision_level_here != conflict_decision_level &&
        decision_level_here > backtracked_decision_level) {
      backtracked_decision_level = decision_level_here;
    }
  }
  for (int i = 0; i < literals.size(); i++) {
    if (literal_decision_level[i] > backtracked_decision_level) {
      unassign_literal(i);
    }
  }
  return backtracked_decision_level; // return the level we are at now
}

// Resolving clauses
vector<int> &CDCL_solver::resolve(vector<int> &input_clause, int literal) {
  // get the second clause
  vector<int> second_input =
      literal_list_per_clause[literal_antecedent[literal]];
  // concatenate the two
  input_clause.insert(input_clause.end(), second_input.begin(),
                      second_input.end());
  for (int i = 0; i < input_clause.size(); i++) {
    // remove the literal from the concatenated version
    if (input_clause[i] == literal + 1 || input_clause[i] == -literal - 1) {
      input_clause.erase(input_clause.begin() + i);
      i--;
    }
  }
  // remove duplicates from the result
  sort(input_clause.begin(), input_clause.end());
  input_clause.erase(unique(input_clause.begin(), input_clause.end()),
                     input_clause.end());
  return input_clause;
}

// Pick the branching variable
int CDCL_solver::pick_branching_variable() {
  // to generate a random integer between 1 and 10, for deciding the mechanism
  // of choosing
  uniform_int_distribution<int> choose_branch(1, 10);
  // to generate a random integer corrsponding to the index of one of the
  // literals
  uniform_int_distribution<int> choose_literal(0, var_count - 1);
  int random_value = choose_branch(generator); // get the value to choose the
                                               // branch if we have spent too
                                               // long trying to randomly find
                                               // an unassigned variable
  bool too_many_attempts = false;
  // number of attempts to find an unassigned variable randomly so far
  int attempt_counter = 0;
  do {
    // Some heuristics to choose the next var
    if (random_value > 4 || assigned_literal_count < var_count / 2 ||
        too_many_attempts) {
      pick_counter++; // increment the number of picks so far this way
      if (pick_counter == 20 * var_count) {
        for (int i = 0; i < literals.size(); i++) {
          original_var_freq[i] /= 2;
          if (literal_frequency[i] != -1) {
            literal_frequency[i] /= 2;
          }
        }
        pick_counter = 0; // reset pick counter
      }
      // find the variable with the highest frequency out of those unassigned
      int variable = distance(
          literal_frequency.begin(),
          max_element(literal_frequency.begin(), literal_frequency.end()));
      // choose assignment based on which polarity is greater
      if (literal_polarity[variable] >= 0) {
        return variable + 1;
      }
      return -variable - 1;
    } else // we pick the variable randomly
    {
      while (attempt_counter < 10 * var_count) {
        int variable = choose_literal(generator);
        if (literal_frequency[variable] != -1) {
          if (literal_polarity[variable] >= 0) {
            return variable + 1;
          }
          return -variable - 1;
        }
        attempt_counter++;
      }
      too_many_attempts = true; // we have attempted too many times
    }
  } while (too_many_attempts);
}

// Just to check all variables are assigned pretty self explainatory
bool CDCL_solver::all_variables_assigned() {
  return var_count == assigned_literal_count;
}

// Show the result
void CDCL_solver::show_result(int result_status) {
  if (result_status == RetVal::sat_c) // if the formula is satisfiable
  {
    // Printing the result
    cout << "SAT" << endl;
    for (int i = 0; i < literals.size(); i++) {
      if (i != 0) {
        cout << " ";
      }
      if (literals[i] != -1) {
        cout << pow(-1, (literals[i] + 1)) * (i + 1);
      } else // assign the unassigned variables to 1

      {
        cout << (i + 1);
      }
    }
    cout << " 0";
  } else // if the formula is unsatisfiable
  {
    cout << "UNSAT";
  }
}

// Function to solve and show result
void CDCL_solver::solve() {
  int result_status = CDCL();
  show_result(result_status);
}

// Main call
int main() {
  CDCL_solver solver;
  solver.initialize();
  solver.solve();
  return 0;
}
