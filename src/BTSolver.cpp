#include"BTSolver.hpp"

using namespace std;

// =====================================================================
// Constructors
// =====================================================================

BTSolver::BTSolver ( SudokuBoard input, Trail* _trail,  string val_sh, string var_sh, string cc )
: sudokuGrid( input.get_p(), input.get_q(), input.get_board() ), network( input )
{
	valHeuristics = val_sh;
	varHeuristics = var_sh; 
	cChecks =  cc;

	trail = _trail;
}

// =====================================================================
// Consistency Checks
// =====================================================================

// Basic consistency check, no propagation done
bool BTSolver::assignmentsCheck ( void )
{
	for ( Constraint c : network.getConstraints() )
		if ( ! c.isConsistent() )
			return false;

	return true;
}

// =================================================================
// Arc Consistency
// =================================================================
bool BTSolver::arcConsistency ( void )
{
    vector<Variable*> toAssign;
    vector<Constraint*> RMC = network.getModifiedConstraints();
    for (int i = 0; i < RMC.size(); ++i)
    {
        vector<Variable*> LV = RMC[i]->vars;
        for (int j = 0; j < LV.size(); ++j)
        {
            if(LV[j]->isAssigned())
            {
                vector<Variable*> Neighbors = network.getNeighborsOfVariable(LV[j]);
                int assignedValue = LV[j]->getAssignment();
                for (int k = 0; k < Neighbors.size(); ++k)
                {
                    Domain D = Neighbors[k]->getDomain();
                    if(D.contains(assignedValue))
                    {
                        if (D.size() == 1)
                            return false;
                        if (D.size() == 2)
                            toAssign.push_back(Neighbors[k]);
                        trail->push(Neighbors[k]);
                        Neighbors[k]->removeValueFromDomain(assignedValue);
                    }
                }
            }
        }
    }
    if (!toAssign.empty())
    {
        for (int i = 0; i < toAssign.size(); ++i)
        {
            Domain D = toAssign[i]->getDomain();
            vector<int> assign = D.getValues();
            trail->push(toAssign[i]);
            toAssign[i]->assignValue(assign[0]);
        }
        return arcConsistency();
    }
    return network.isConsistent();
}

/**
 * Part 1 TODO: Implement the Forward Checking Heuristic
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
 * 		   The bool is true if assignment is consistent, false otherwise.
 */
pair<map<Variable*,Domain>,bool> BTSolver::forwardChecking ( void )
{
	map<Variable*, Domain> variable_changes;
	unordered_set<Variable*> assigned;
	int assignment;
	Domain D;
	
	for (Constraint& c : network.getConstraints()) {
		for ( Variable* var: c.vars ) {
			if (var->getDomain().size() == 0) return make_pair(variable_changes, false); 
			if ( var->isModified() ) {
				var->setModified( false ); 
				assignment = var->getAssignment();
				if (assignment && assigned.find(var) == assigned.end()){
					assigned.insert(var);
					for (Variable* neighbor : network.getNeighborsOfVariable(var)) {
						D = neighbor->getDomain();
						if (!neighbor->isAssigned()) {
							if (D.contains(assignment)) {
								if (D.size() == 1) return make_pair(variable_changes, false);
								trail->push(neighbor);
								neighbor->removeValueFromDomain(assignment);
								variable_changes[neighbor] = D;
								neighbor->setModified(false);
							}
						}
					}
				}	
			}
		}
	}
	return make_pair(variable_changes, true);
}

/**
 * Part 2 TODO: Implement both of Norvig's Heuristics
 *
 * This function will do both Constraint Propagation and check
 * the consistency of the network
 *
 * (1) If a variable is assigned then eliminate that value from
 *     the square's neighbors.
 *
 * (2) If a constraint has only one possible place for a value
 *     then put the value there.
 *
 * Note: remember to trail.push variables before you change their domain
 * Return: a pair of a map and a bool. The map contains the pointers to all variables that were assigned during 
 *         the whole NorvigCheck propagation, and mapped to the values that they were assigned. 
 *         The bool is true if assignment is consistent, false otherwise.
 */


bool norvigHelper(map<Variable*, int>& variable_changes, Variable* var, ConstraintNetwork& network, Trail* trail, BTSolver* B) {
	Domain D;
	int assignment = var->getAssignment();
	
	if (B->forwardChecking().second) {
		for (Variable* neighbor : network.getNeighborsOfVariable(var)) {
			D = neighbor->getDomain();
			if (D.size() == 1 && !neighbor->isAssigned()) {	
				if (D.contains(assignment)) return false;
				assignment = D.getValues().at(0);
				trail->push(neighbor);
				neighbor->assignValue(assignment);
				variable_changes[neighbor] = assignment;
				if (!norvigHelper(variable_changes, neighbor, network, trail, B)) return false;
				break;
			}
		}
	}
	else return false;
	return true;
	
}

pair<map<Variable*,int>,bool> BTSolver::norvigCheck ( void )
{
	map<Variable*, int> variable_changes;
	map<int, int> counts;
	Domain D;
	int assignment;
	if (!BTSolver::forwardChecking().second) return make_pair(variable_changes, false);
	
	
	for (Variable* var : network.getVariables()) {
		D = var->getDomain();
		if (D.size() == 1 && !var->isAssigned()) {
			trail->push(var);
			assignment = D.getValues().at(0);
			var->assignValue(assignment);
			variable_changes[var] = assignment;						
			if (!norvigHelper(variable_changes, var, network, trail, this)) return make_pair(variable_changes, false);
		}
	}


	for (Constraint& c : network.getConstraints()) {
		counts.clear();
		for ( Variable* var: c.vars ) {
			for (int i : var->getDomain().getValues()) {
				if (!counts.count(i)) counts[i] = 1;
				else counts[i] = counts[i] + 1;
			}
		}

		for (int i = 1; i <= sudokuGrid.get_n(); ++i) {
			if (counts.find(i) == counts.end()) return make_pair(variable_changes, false);
		}

		for (auto& x : counts) {
			if (x.second == 1) {
				for (Variable* var : c.vars) {
					D = var->getDomain();
					if (D.contains(x.first) && !var->isAssigned()){
						trail->push(var);
						var->assignValue(x.first);
						variable_changes[var] = x.first;						
						for (Variable* neighbor : network.getNeighborsOfVariable(var)) {
							D = neighbor->getDomain();
							if (neighbor->getAssignment() == x.first) return make_pair(variable_changes, false);
							if (!neighbor->isAssigned()) {
								if (D.contains(x.first)) {
									if (D.size() == 1) return make_pair(variable_changes, false);
									trail->push(neighbor);
									neighbor->removeValueFromDomain(x.first);
									neighbor->setModified(false);
								}
								if (D.size() == 1) {
									trail->push(neighbor);
									assignment = D.getValues().at(0);
									neighbor->assignValue(assignment);
									variable_changes[neighbor] = assignment;
								}
							}
						}
						var->setModified(false);
						break;	
					}
				}
			}		
		}
	}
	return make_pair(variable_changes, network.isConsistent());
}

/**
 * Optional TODO: Implement your own advanced Constraint Propagation
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
bool BTSolver::getTournCC ( void )
{
	return BTSolver::norvigCheck().second;
}

// =====================================================================
// Variable Selectors
// =====================================================================

// Basic variable selector, returns first unassigned variable
Variable* BTSolver::getfirstUnassignedVariable ( void )
{
	for ( Variable* v : network.getVariables() )
		if ( !(v->isAssigned()) )
			return v;

	// Everything is assigned
	return nullptr;
}

/**
 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
 *
 * Return: The unassigned variable with the smallest domain
 */
Variable* BTSolver::getMRV ( void )
{
   	Variable* min_val = nullptr;
	int min_size;
	int d;
	for (Variable* v : network.getVariables()) {
		if (!v->isAssigned()) {
			d = v->getDomain().size();
			if (!min_val || min_size > d) {
				min_val = v;
				min_size = d;
			}
			if (d == 1) return v;
		}
	}
	return min_val;
}

/**
 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
 *                with Degree Heuristic as a Tie Breaker
 *
 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
 * 		   If there are multiple variables that have the same smallest domain with the same number 
 * 		   of unassigned neighbors, add them to the vector of Variables.
 *         If there is only one variable, return the vector of size 1 containing that variable.
 */
vector<Variable*> BTSolver::MRVwithTieBreaker ( void )
{
	unordered_set<Variable*> min_sizes;
	vector<Variable*> return_vars;
	int min_size = -1;
	int d;
	
	for ( Variable* v : network.getVariables() ) {
		if (!(v->isAssigned())) {
			d = v->getDomain().size();
			if (min_size == -1) {
				min_size = d;
				min_sizes.insert(v);
			}
			else if (d < min_size) {
				min_sizes.clear();
				min_size = d;
				min_sizes.insert(v);
			}
			else if (d == min_size) {
				min_sizes.insert(v);
			}
		}
	}

	if (min_size == -1) {
		return_vars.push_back(nullptr);
		return return_vars;
	}
	else if (min_sizes.size() == 1) {
		for (Variable* var : min_sizes)
			return_vars.push_back(var);
		return return_vars;
	}
	
	int neighbors;
	int max_neighbors = -1;
 
	for (Variable* v : min_sizes) {
		neighbors = 0;
		for (Variable* var : network.getNeighborsOfVariable(v)) 
			if (!(var->isAssigned())) neighbors += 1; 
		
		if (neighbors > max_neighbors) {
			return_vars.clear();
			max_neighbors = neighbors;
			return_vars.push_back(v);
		}
		else if (neighbors == max_neighbors) return_vars.push_back(v);
		
	}
	
	return return_vars;
}
/**
 * Optional TODO: Implement your own advanced Variable Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
Variable* BTSolver::getTournVar ( void )
{
	return BTSolver::MRVwithTieBreaker().at(0);
}

// =====================================================================
// Value Selectors
// =====================================================================

// Default Value Ordering
vector<int> BTSolver::getValuesInOrder ( Variable* v )
{
	vector<int> values = v->getDomain().getValues();
	sort( values.begin(), values.end() );
	return values;
}

/**
 * Part 1 TODO: Implement the Least Constraining Value Heuristic
 *
 * The Least constraining value is the one that will knock the least
 * values out of it's neighbors domain.
 *
 * Return: A list of v's domain sorted by the LCV heuristic
 *         The LCV is first and the MCV is last
 */

vector<int> BTSolver::getValuesLCVOrder ( Variable* v )
{
	vector<pair<int, int>> values;
	vector<int> return_vec;
	int count;
	Domain current;
	for (int val : v->getDomain().getValues()) {
		count = 0;
		for(Variable* neighbor : network.getNeighborsOfVariable(v)) {
			if (!neighbor->isAssigned()) {
				if (neighbor->getDomain().contains(val)) count +=1;
			}	
		}
		values.push_back(make_pair(count, val));
	}

	sort(values.begin(), values.end());
	
	for (auto elem : values){
		return_vec.push_back(elem.second);
	}
	
	return return_vec;
}
/**
 * Optional TODO: Implement your own advanced Value Heuristic
 *
 * Completing the three tourn heuristic will automatically enter
 * your program into a tournament.
 */
vector<int> BTSolver::getTournVal ( Variable* v )
{
	return BTSolver::getValuesLCVOrder(v);
}

// =====================================================================
// Engine Functions
// =====================================================================

int BTSolver::solve ( float time_left)
{
	if (time_left <= 60.0)
		return -1;
	double elapsed_time = 0.0;
    clock_t begin_clock = clock();

	if ( hasSolution )
		return 0;

	// Variable Selection
	Variable* v = selectNextVariable();

	if ( v == nullptr )
	{
		for ( Variable* var : network.getVariables() )
		{
			// If all variables haven't been assigned
			if ( ! ( var->isAssigned() ) )
			{
				return 0;
			}
		}

		// Success
		hasSolution = true;
		return 0;
	}

	// Attempt to assign a value
	for ( int i : getNextValues( v ) )
	{
		// Store place in trail and push variable's state on trail
		trail->placeTrailMarker();
		trail->push( v );

		// Assign the value
		v->assignValue( i );

		// Propagate constraints, check consistency, recurse
		if ( checkConsistency() ) {
			clock_t end_clock = clock();
			elapsed_time += (float)(end_clock - begin_clock)/ CLOCKS_PER_SEC;
			double new_start_time = time_left - elapsed_time;
			int check_status = solve(new_start_time);
			if(check_status == -1) {
			    return -1;
			}
			
		}

		// If this assignment succeeded, return
		if ( hasSolution )
			return 0;

		// Otherwise backtrack
		trail->undo();
	}
	return 0;
}

bool BTSolver::checkConsistency ( void )
{
	if ( cChecks == "forwardChecking" )
		return forwardChecking().second;

	if ( cChecks == "norvigCheck" )
		return norvigCheck().second;

	if ( cChecks == "tournCC" )
		return getTournCC();

	return assignmentsCheck();
}

Variable* BTSolver::selectNextVariable ( void )
{
	if ( varHeuristics == "MinimumRemainingValue" )
		return getMRV();

	if ( varHeuristics == "MRVwithTieBreaker" )
		return MRVwithTieBreaker()[0];

	if ( varHeuristics == "tournVar" )
		return getTournVar();

	return getfirstUnassignedVariable();
}

vector<int> BTSolver::getNextValues ( Variable* v )
{
	if ( valHeuristics == "LeastConstrainingValue" )
		return getValuesLCVOrder( v );

	if ( valHeuristics == "tournVal" )
		return getTournVal( v );

	return getValuesInOrder( v );
}

bool BTSolver::haveSolution ( void )
{
	return hasSolution;
}

SudokuBoard BTSolver::getSolution ( void )
{
	return network.toSudokuBoard ( sudokuGrid.get_p(), sudokuGrid.get_q() );
}

ConstraintNetwork BTSolver::getNetwork ( void )
{
	return network;
}
