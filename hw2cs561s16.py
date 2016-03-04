import sys
import collections

fact_list = []
input_query = []
std_facts = []
OPRS = ['&&', '=>']
brk_flag =False

prd_query = []

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
            # print '******'
            # print op
            sen.append(op)
            i += 1
            continue
        elif isinstance(f[i], str):
            # print "'"+ f[i] +"'",
            name = f[i]
            if isinstance(f[i+1], list):
                # print f[i+1]
                args = f[i+1]
            # print '******'
            # print name
            # print args
            predicate = Predicate(name, args)
            # print predicate
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
            # input_query.append(query)
            print '!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11'
            print input_query
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
    # print '\n\n\nCREATING KB\n'

    for prd in prd_sentences:
        print prd
        if '=>' in prd:     # this is a rule
            implication_pos = prd.index('=>')
            # print 'Implication'
            lhs = prd[:implication_pos]
            rhs = prd[implication_pos + 1:]
            # print lhs
            # print rhs
            if rhs[0].name in KB.rules:      # Append
                KB.rules[rhs[0].name].append(prd)
            else:
                KB.rules[rhs[0].name] = [prd]
                # print 'Inserted IMP into KB'
                # print KB.rules[rhs[0].name]
        else:   # this is a fact
            # print "Fact"
            # print prd
            if prd[0].name in KB.rules:
                KB.rules[prd[0].name].append(prd)
            else:
                KB.rules[prd[0].name] = [prd]
                # print 'Inserted RULE into KB'
                # print KB.rules[prd[0].name]

    # print '\n\nFINAL KB^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\n'
    # print 'Facts'
    # for k in KB.facts:
    #     print KB.facts[k]
    # # return KB

    # print '\n\nRules'
    # for k in KB.rules:
    #     print KB.rules[k]

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
    # print 'STD RULE IS'
    # print std_rule
    std_facts.append(std_rule)
    if '=>' in std_rule:
        impl_pos = std_rule.index('=>')
        lhs.extend(std_rule[:impl_pos])
        rhs.extend(std_rule[impl_pos + 1:])
        # print 'LHS:',
        # print lhs
        # print 'RHS:',
        # print rhs

        if lhs != []:
            # print 'REMOVING &&'
            lhs = [x for x in lhs if x != '&&']
            # print lhs

    else:   # retrun fact
        rhs = sen

    return lhs, rhs


def subst(theta, first):
    # print "\n\nSubstitution"
    # print "DICT::"
    # print theta
    # print first
    new_args = []
    if not isinstance(first, Predicate):
        # print 'Incorrect First passed'
        # print first
        return None
    else:
        for arg in first.args:
            if arg in theta:
                new_args.append(theta[arg])
            else:
                new_args.append(arg)
        new_first = Predicate(first.name, new_args)
        # print "NEW FIRST"
        # print new_first
        return new_first





def unify(x, y, subst = {}):
    global x_y


    # print "Unifying"
    # print x
    # print y

    if subst is None:
        # print "Failure"
        # failure is denoted by None (default is {})
        return None
    elif x == y:
        # happens if both x and y same-name variables, return the most general unifier
        # print "Same variable"
        # print x
        # print y
        return subst
    # the following two cases are the only cases that can cause a binding
    elif is_variable(x):
        # print 'X is variable'
        # print x
        # print y
        return unify_vars(x, y, subst)
    elif is_variable(y):
        # print 'X is variable'
        # print x
        # print y
        return unify_vars(y, x, subst)
    elif isinstance(x, Predicate) and isinstance(y, Predicate):
        del x_y[:]
        x_y.append(x)
        x_y.append(y)
        # print 'X and Y PREDICATE'
        # print x
        # print y
        # to merge two clauses the operands must be the same
        # if they are then unify their arguments
        return unify(x.args, y.args, subst)
    elif isinstance(x, list) and isinstance(y, list) and len(x) == len(y):
        # this is the case when we're unifying the arguments of a clause
        # see preceding line
        # print 'X and Y LIST'
        # print x
        # print y
        return unify(x[1:], y[1:], unify(x[0], y[0], subst))
    else:
        # does not match any case, so no substitution
        # print '\n-----------------------------------------------------------------------'
        # print 'UNIFYING'
        # print x_y[0]
        # print x_y[1]

        # print '-----------------------------------------------------------------------\n'
        # write_false()
        # write_false()
        return None


def unify_vars(var, x, subst):
    if var in subst:
        # if binding is already in the dict simply return it
        return unify(subst[var], x, subst)
    elif x in subst:
        return unify(var, subst[x], subst)
    else:
        subst_copy = subst.copy()
        subst_copy[var] = x
        return subst_copy


def write_false():
    global x_y

    output.write('False: ')
    output.write(str(x_y[1]))
    output.write('\n')



def is_variable(item):
    # print 'Checking if variable:'
    # print item
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

    goal_rules = KB.rules[goal.name]
    ask_flag = True
    for rule in goal_rules:
        # print '.................................................'
        # print rule
        # print '.................................................'
        lhs, rhs = standardize_vbls(rule)



        if lhs: # its a rule
            write_ask(goal, theta)
            ask_flag = True
        elif ask_flag:
            print '.................................................'
            print goal
            print theta
            print '.................................................'
            write_ask(goal, theta)
            ask_flag = False
        #
        # else:   # its a fact
        #
        #     for arg in goal.args:
        #         if is_variable(arg):
        #             ask_flag = True
        #             break
        #     if ask_flag:
        #          write_ask(goal, theta)
        #          ask_flag = False

        for theta1 in fol_bc_and(KB, lhs, unify(rhs[0], goal, theta)):
            brk_flag = write_true(goal, theta1)
            # if brk_flag:
            #     break
            yield theta1

    # ask_flag = True
    # Best place now
    # write_false()


def fol_bc_and(KB, goals, theta):
    # print '~~~~~~~~~~~~~~~~~~~~~~~~~'
    # print 'GOALS'
    # print goals
    #
    # print theta
    # print '++++++++++++++++++++++++++\n\n'
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
        write_false()




def write_ask(goal, theta):
    # return false if goal cannot be satisfied in facts
    # return true if goal can be satisfied in
    output.write('Ask: ' + goal.name + '(')
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
            # print arg
    output.write(')\n')

    # if ()


def write_true(goal, theta):
    global input_query
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
            # print arg
    output.write(')\n')

    pq = prd_query[0]

    if pq.name == goal.name:
        print pq
        print goal
        cut_off_flag = True
        for i in range(len(pq.args)):
            if is_variable(pq.args[i]):
                if theta.get(pq.args[i]):
                    print 'Variable assigned', pq.args[i]
                    print theta.get(pq.args[i])
                    continue
                else:   # value unassigned
                    cut_off_flag = False
                    break
            else:   # each constant must match
                if pq.args[i] == goal.args[i]:
                    print 'MATCH CONST'
                    print pq.args[i], goal.args[i]
                    cut_off_flag = True
                else:
                    cut_off_flag = False
                    print 'MISMATCH CONST'
                    print pq.args[i], goal.args[i]
                    break
        if cut_off_flag:
            output.write('True')
            quit()
            return True
    return False
    # print str_repr
    # print theta1


def main():
    global fact_list
    global input_query
    global std_facts
    global output
    global prd_query
    prd_sentences = []

    file_name = sys.argv[2]
    process_input(file_name)

    prd_query = convert_to_predicate(input_query)
    for f in fact_list:
        sen = convert_to_predicate(f)
        prd_sentences.append(sen)

    # print "\n\nSENTENCES\n"
    # for s in prd_sentences:
    #     for p in s:
    #         if isinstance(p, Predicate):
    #             print 'Function: ' + p.name
    #             print 'Arguments:' + str(p.args)
    #         else:
    #             print p
    print "\n\nQUERY\n"
    print prd_query[0].name
    print prd_query[0].args

    KB = construct_kb(prd_sentences)

    # print "\n\n\nTESTING IMPL!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
    goal_rules = KB.rules[prd_query[0].name]
    # temp = {}
    print goal_rules
    print '\n\n\n'
    # for rule in goal_rules:
    #     print rule
    #     # print KB.rules[rule]
    #     if '=>' in rule:
    #         impl_pos = rule.index('=>')
    #         lhs = rule[:impl_pos]
    #         rhs = rule[impl_pos + 1:]
    #         print 'LHS: ',
    #         print lhs
    #         print 'RHS: ',
    #         print rhs
    #         print 'CALLING UNIFY$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$'
    #         temp = unify(rhs[0], prd_query[0], temp)
    #     else:
    #         print rule
    # print "\n\n\nTESTING UNIFY####################!!!!!!!!!!!!!!!!!!!!11"
    # if temp is None:
    #     print "NO UNIFICATION"
    # else:
    #     for k in temp:
    #         print 'KEY:',
    #         print k
    #         print 'VAL:',
    #         print temp[k]

    # lhs = []
    # temp = unify()

    # std = collections.OrderedDict()
    # print "TESTING STANDATD @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@"
    # for rule in goal_rules:
    #     lhs, rhs = standardize_vbls(rule, std)
    # print "STD DICT"
    # for k in std:
    #     print 'KEY:',
    #     print k
    #     print 'VAL:',
    #     print std[k]
    #     print "----------------------------------STD RULE RETURNED----------------------------------------------"
    #     print lhs
    #     print rhs
    #     print '--------------------------------------------------------------------------------------------------'

    print '%%%%%%%%%%%'
    print prd_query[0]
    # for case 4 loop over all queries in prd_query and change the global query being evaluated

    final_theta = fol_bc_ask(KB, prd_query[0])


    print '\n\n\n********************************FINAL THETA**************************'
    check = [x for x in final_theta]
    if check == []:
        output.write("False")
    else:
        output.write('True')

    # print '^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^'
    # print check
    # print '^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^'
    # if final_theta is None:
    #     print "False"
    #
    # else:
    #     # print final_theta
    #     print '!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!TRUE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!1'
    #     for k in final_theta:
    #         print 'Key:',
    #         print k


    # print '\n\n\n********************************STD SEN**************************'
    # for sen in std_facts:
    #     print sen

    output.close()

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