### TEAM MEMBERS
## MEMBER 1: 210050053
## MEMBER 2: 210050117
## MEMBER 3: 210050118


from z3 import *
import sys

file = sys.argv[1]

with open(file) as f:
	n,T = [int(x) for x in next(f).split()]
	matrix = []
	for line in f:
		matrix.append([int(x) for x in line.split()])


num=T+1

X=[] # matrix
comp_c=[] # comparing two adajacent matrices condition

X.append(matrix) # initialising the matrix

# THIS ARRAYS STORE THE TRANSITIONS DONE IN EACH STEP 
# THIS PARTICULAR ENTITY IS OF THE FORM n*(num) + i + 1
# num = number of the row/column
# i belongs [0,1,2,3]
# i = 2*(column?)+(right?||down?)
# 1 is to avoid collision

mix = []

mix.append([ Int("h_%s" % (i)) for i in range(num) ]) # variables for left/right/up/down

# removing the extra bracket
mix = mix[0]

# initialising the arrays
mix_c =[]
# Conditions on mix
mix_c=mix_c + ([ And(0 <= mix[i],mix[i] <= 4*n)
                for i in range(num) ])
# CONDITIONS LIST
comp_c = []

for k in range(1,num):
        # APPENDING EACH MATRIX INTO X
        X.append([ [ Int("x_%s_%s_%s" % (k,i+1, j+1)) for j in range(n) ]
            for i in range(n) ])
        # THIS IS THE CLAUSE FOR THE TRANSITION OF iTH ROW LEFT SHIFT
        for i in range(n):
            c1 = (mix[k] == i +1)
            x = True
            for p in range(n):
                for q in range(n):
                    if(p==i):
                        o = X[k][p][q] == X[k-1][p][(q+1)%n]
                        x = Implies(c1,o)
                        comp_c += [x]
                        
                    else:
                        o = (X[k][p][q] == X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
        # THIS IS THE CLAUSE FOR THE TRANSITION OF iTH ROW RIGHT SHIFT    
        for i in range(n):
            c1 = (mix[k] == n+i+1)
            x = True
            for p in range(n):
                for q in range(n):
                    if(p==i):
                        o = X[k][p][q] == X[k-1][p][(q-1)%n]
                        x = Implies(c1,o)
                        comp_c += [x]
                        
                    else:
                        o = (X[k][p][q] == X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
        # THIS IS THE CLAUSE FOR THE TRANSITION OF iTH COLUMN UP SHIFT
        for i in range(n):
            c1 = (mix[k] == 2*n+i+1 )
            x = True
            for p in range(n):
                for q in range(n):
                    if(q==i):
                        o = X[k][p][q] == X[k-1][(p+1)%n][q]
                        x = Implies(c1,o)
                        comp_c += [x]
                        
                    else:
                        o = (X[k][p][q] == X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
        # THIS IS THE CLAUSE FOR THE TRANSITION OF iTH COLUMN DOWN SHIFT
        for i in range(n):
            c1 = (mix[k] == 3*n+i+1)
            x = True
            for p in range(n):
                for q in range(n):
                    if(q==i):
                        o = X[k][p][q] == X[k-1][(p-1)%n][q]
                        x = Implies(c1,o)
                        comp_c += [x]
                        
                    else:
                        o = (X[k][p][q] ==   X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]
        # THIS IS THE CLAUSE FOR NO TRANSITION (NOP OPERATION KINDA...)
        for i in range(n):
            c1 = (mix[k] == 0)
            x = True
            for p in range(n):
                for q in range(n):
                        o = (X[k][p][q] ==   X[k-1][p][q])
                        x = Implies(c1,o)
                        comp_c += [x]

# ADDING THE FINAL CLAUSE FOR THE LAST MATRIX TO MATCH WITH THE REQUIRED MATRIX       	   
comp_c+=[And(X[num-1][i][j]==n*i+j+1) for i in range(n) for j in range(n) ]

# INITIALING THE SOLVER
s = Solver()

# ADDING THE CLAUSES TO THE SOLVER
s.add(comp_c+mix_c)

# CALLING THE CHECK FUNCTION
r = s.check()

print(r)

if r == sat:
    m = s.model()
    for k in range(1,num):
       
        r = [ [ m.evaluate(X[k][i][j]) for j in range(n) ]
            for i in range(n) ]

    g1 = [m.evaluate((mix[k]-1)%n).as_long() for k in range(num)]
    g2 = [m.evaluate(((mix[k]-1)/n)/2).as_long() for k in range(num)]
    g3 = [m.evaluate(((mix[k]-1)/n)%2).as_long() for k in range(num)]
    x=[['l','r'],
        ['u','d']]

    for k in range(1,num):
        if (g2[k]<0 or g1[k]<0):
            continue
        print(str(g1[k])+x[g2[k]][g3[k]])