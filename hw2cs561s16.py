import sys
import collections
import copy

fact_list = []
input_query = []
std_facts = []
OPRS = ['&&', '=>']
brk_flag =False
prev_log = ''
i_prd_query = []
i_query_len = 0
curr_goal_len = 0
ask_flag = True
x_y = []
parent_predicate = []

output = open('output.txt', 'w')


VARIABLE_COUNTER = 0


class KnowledgeBase:
    def __init__(self):
        self.rules = collections.OrderedDict()
        # self.facts = collections.OrderedDict()


class Predicate:
    def __init__(self,name, args=[]):
        self.name = name
        self.args = args

    def __repr__(self):
        str_repr  = ''
        str_repr += str(self.name) + '('
        str_repr += self.args[0]
        for a in self.args[1:]:
             str_repr += ', ' + a
        str_repr += ')'
        return str_repr


def convert_to_predicate(f):
    sen = []
    for i in range(len(f)):
        if f[i] in OPRS:
            op = f[i]
            sen.append(op)
            i += 1
            continue
        elif isinstance(f[i], str):
            name = f[i]
            if isinstance(f[i+1], list):
                args = f[i+1]
            predicate = Predicate(name, args)
            sen.append(predicate)
            i += 2
            continue
    return sen


def pre_parse_facts(fact):
    fact = '(' + fact + ')'
    fact = fact.replace('(', ' ( ')
    fact = fact.replace(')', ' ) ')
    fact = fact.replace(', ', ' ')
    fact_lst = fact.split()
    fact_lst = parse_facts(fact_lst)
    return fact_lst


def parse_facts(fact_lst):
    first_token = fact_lst.pop(0)

    if first_token == '(':
        # start of a new expression
        new_expression = []
        while fact_lst[0] != ')':
            # keep appending values to the new expression list
            new_expression.append(parse_facts(fact_lst))
        # remove  the ')'
        fact_lst.pop(0)
        return new_expression
    else:
        # code is here means token is not the start of a new expression
        return first_token
#


def process_input(fn):
    # global ip_query
    # global KB
    global fact_list
    global input_query
    file_handle = open(fn, "r")
    line_counter = 0

    for line in file_handle:
        if line_counter == 0:
            q = line.strip('\n\r')
            input_query = pre_parse_facts(q)
            line_counter += 1
            continue
        if line_counter == 1:
            fact_count = int(line.strip('\n\r'))
            line_counter += 1
            continue
        if line_counter >= 2:
            fact = line.strip('\n\r')
            a_fact_list = pre_parse_facts(fact)
            fact_list.append(a_fact_list)
            continue

    return


def construct_kb(prd_sentences):
    KB = KnowledgeBase()

    for prd in prd_sentences:
        if '=>' in prd:     # this is a rule
            implication_pos = prd.index('=>')
            lhs = prd[:implication_pos]
            rhs = prd[implication_pos + 1:]
            if rhs[0].name in KB.rules:      # Append
                KB.rules[rhs[0].name].append(prd)
            else:
                KB.rules[rhs[0].name] = [prd]
        else:   # this is a fact
            if prd[0].name in KB.rules:
                KB.rules[prd[0].name].append(prd)
            else:
                KB.rules[prd[0].name] = [prd]

    return KB




def standardize_vbls(sen, stdized = None):
    global VARIABLE_COUNTER
    global std_facts
    std_rule = []
    if stdized is None:
        stdized = collections.OrderedDict()

    for prd in sen:
        if isinstance(prd, Predicate):
            std_args = []
            for var in prd.args:
                if is_variable(var):
                    # check if var has already been standardized
                    if var in stdized:
                        # Do nothing
                        # return stdized[var]
                        std_args.append(stdized[var])
                        continue
                    else:
                        new_var = 'v_' + str(VARIABLE_COUNTER)
                        stdized[var] = new_var
                        std_args.append(new_var)
                        VARIABLE_COUNTER += 1
                else: # its a constant
                    std_args.append(var)
            new_prd = Predicate(prd.name, std_args)
            std_rule.append(new_prd)
        else:   # Not a predicate then append opr
            std_rule.append(prd)

    lhs = []
    rhs = []
    std_facts.append(std_rule)
    if '=>' in std_rule:
        impl_pos = std_rule.index('=>')
        lhs.extend(std_rule[:impl_pos])
        rhs.extend(std_rule[impl_pos + 1:])

        if lhs != []:
            lhs = [x for x in lhs if x != '&&']

    else:   # retrun fact
        rhs = sen

    return lhs, rhs


def subst(theta, first):
    new_args = []
    if not isinstance(first, Predicate):
        return None
    else:
        for arg in first.args:
            if arg in theta:
                new_args.append(theta[arg])
            else:
                new_args.append(arg)
        new_first = Predicate(first.name, new_args)
        return new_first


def unify(x, y, subst = {}):
    global x_y
    global ask_flag
    global brk_flag
    if subst is None:
        # failure is denoted by None (default is {})
        return None
    elif x == y:
        # happens if both x and y same-name variables, return the most general unifier
        return subst
    # the following two cases are the only cases that can cause a binding
    elif is_variable(x):
        return unify_vars(x, y, subst)
    elif is_variable(y):
        return unify_vars(y, x, subst)
    elif isinstance(x, Predicate) and isinstance(y, Predicate):
        del x_y[:]
        x_y.append(x)
        x_y.append(y)
        # to merge two clauses the operands must be the same
        # if they are then unify their arguments
        return unify(x.args, y.args, subst)
    elif isinstance(x, list) and isinstance(y, list) and len(x) == len(y):
        # this is the case when we're unifying the arguments of a clause
        # see preceding line
        return unify(x[1:], y[1:], unify(x[0], y[0], subst))
    else:
        # does not match any case, so no substitution
        # ask_flag = write_false()
        brk_flag = True
        return None


def unify_vars(var, x, subst):
    if var in subst:
        # if binding is already in the dict simply return it
        return unify(subst[var], x, subst)
    elif x in subst:
        return unify(var, subst[x], subst)
    else:
        # subst_copy = subst.copy()
        subst_copy = copy.deepcopy(subst)
        subst_copy[var] = x
        return subst_copy


def write_false():
    # global ask_flag
    global brk_flag
    global x_y
    global prev_log
    write_flag = True
    #
    if not prev_log == "Ask":
        prev_log = "False"
        # return False

    for arg in x_y[1].args:
        if is_variable(arg):
            write_flag = False
            break
    if write_flag:
        if brk_flag:
            output.write('False: ')
            output.write(str(x_y[1]))
            prev_log = 'False: ' + str(x_y[1])
            output.write('\n')
            brk_flag = False
            return True
    else:
        return False


def is_variable(item):
    if isinstance(item, Predicate):
        return False
    elif isinstance(item, list):
        return False
    else:
        return item[0].islower()


def fol_bc_ask(KB, query):
    theta = collections.OrderedDict()
    return fol_bc_or(KB, query, theta)


def fol_bc_or(KB, goal, theta):
    global parent_predicate
    global brk_flag
    global ask_flag
    global x_y
    global prev_log

    goal_rules = KB.rules[goal.name]
    ask_flag = True

    print '\n\n'
    print 'Inside FOL-BC-OR'
    print goal
    print goal_rules
    for rule in goal_rules:
        lhs, rhs = standardize_vbls(rule)

        if lhs: # its a rule
            write_ask(goal, theta)
            ask_flag = True

        elif ask_flag:
            write_ask(goal, theta)
            ask_flag = False
        for theta1 in fol_bc_and(KB, lhs, unify(rhs[0], goal, theta)):
            brk_flag = write_true(goal, theta1)
            yield theta1
    # Best place now
    print 'Writing false'
    print goal
    print theta
    print prev_log
    x_y[1] = goal
    ask_flag = write_false()


def fol_bc_and(KB, goals, theta):
    global ask_flag

    print '\n\n'
    print 'Inside FOL-BC-AND'
    print goals


    if theta is None:
        pass

    elif len(goals) == 0:
        yield theta

    else:
        first = goals[0]
        rest = goals[1:]
        for theta1 in fol_bc_or(KB, subst(theta, first), theta):
            for theta2 in fol_bc_and(KB, rest, theta1):
                yield theta2
        # write_false()
        # ask_flag = write_false()


def write_ask(goal, theta):
    # return false if goal cannot be satisfied in facts
    # return true if goal can be satisfied in
    global prev_log

    output.write('Ask: ' + goal.name + '(')
    prev_log = "Ask"
    str_repr = goal.args[0]
    if str_repr[0].islower():
        if str_repr in theta.keys():
            str_repr = theta.get(str_repr)
            output.write(str_repr)
        else:
            str_repr = '_'
            output.write(str_repr)
    else:
        output.write(str_repr)
    for arg in goal.args[1:]:
        if arg[0].islower():
            if str_repr in theta.keys():
                str_repr = theta.get(str_repr)
                output.write(', ' + str_repr)
            else:
                str_repr = ', _'
                output.write(str_repr)
        else:
            output.write(', ' + arg)
    output.write(')\n')


def write_true(goal, theta):
    global input_query
    global curr_goal_len
    global i_query_len
    global ask_flag
    global prev_log
    prev_log = "True"
    # Need to cut off here if goal matches input query
    output.write('True: ' + goal.name + '(' )
    str_repr = goal.args[0]
    if str_repr[0].islower():
        str_repr = theta.get(str_repr)
        output.write(str_repr)
    else:
        output.write(str_repr)
    for arg in goal.args[1:]:
        if arg[0].islower():
            output.write(', ' + theta.get(arg))
        else:
            output.write(', ' + arg)
    output.write(')\n')

    pq = i_prd_query
    if pq and goal:
        if pq.name == goal.name:
            cut_off_flag = True
            for i in range(len(pq.args)):
                if is_variable(pq.args[i]):
                    if theta.get(pq.args[i]):
                        continue
                    else:   # value unassigned
                        cut_off_flag = False
                        # return False
                        break
                else:   # each constant must match
                    if pq.args[i] == goal.args[i]:
                        cut_off_flag = True
                    else:
                        cut_off_flag = False
                        # return False
                        break
            if cut_off_flag:
                # return True
                curr_goal_len += 1
                if curr_goal_len == i_query_len: # All goals matched exit
                    output.write('True')
                    # quit()
                    return True
                return True
    return False


def main():
    global fact_list
    global input_query
    global std_facts
    global output
    global i_prd_query
    global i_query_len
    prd_sentences = []

    file_name = sys.argv[2]
    process_input(file_name)

    prd_query = convert_to_predicate(input_query)
    for f in fact_list:
        sen = convert_to_predicate(f)
        prd_sentences.append(sen)

    KB = construct_kb(prd_sentences)

    prd_query = [x for x in prd_query if x != '&&']
    i_query_len = len(prd_query)
    # for case 4 loop over all queries in prd_query and change the global query being evaluated
    flg_file = True

    temp_q_len = 0
    check = []
    for q in prd_query:
        temp_q_len += 1
        check = []
        for i in fol_bc_ask(KB, q):
            check = [x for x in i]
            break
        if check == []:
            temp_str = 'False: ' + str(q)
            if prev_log != temp_str:
                output.write("False: ")
                output.write(str(q))
                output.write('\n')

            output.write("False")
            quit()
        if check and temp_q_len == i_query_len:
            output.write('True')

    output = open('output.txt', 'r')
    lines = output.readlines()
    output.close()

    write = open('output.txt', 'w')
    # write = open('traverse_log.txt', 'w')
    write.writelines([item for item in lines[:-1]])
    item = lines[-1].rstrip()
    write.write(item)
    write.close()


if __name__ == '__main__':
    main()