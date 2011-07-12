----------------------------- MODULE SumAndMax -----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS a

VSCOMPTESTCASE == << 9, 5, 0, 2, 7, 3, 2, 1, 10, 6 >>
N == Len(a)
IndexOfMax(i_max) == IF i_max < 1 THEN 0 ELSE CHOOSE mx \in 1 .. i_max : \A j \in 1 .. i_max : a[j] <= a[mx]
SubMax(i_max) == LET mxIdx == IndexOfMax(i_max)
       IN  a[mxIdx]
Max == SubMax(N)
       
PartialSum[i \in Nat] == IF i>N THEN 0 ELSE a[i] + PartialSum[i+1]  \** computes the partial sum a[i] + ... + a[N]
EltSum == PartialSum[1]

(***************************************************************************
--algorithm SumAndMax {
    variables sum = 0, max = 0, i;
    {
        precond: assert N >= 0 /\ \A j \in 1..N : a[j] >= 0;
        loopinit: i := 1;
        mainloop: while (i <= N) {
            testmax: if (max < a[i]) {
                updatemax: max := a[i];
            };
            updatesum: sum := sum + a[i];
            incloop: i := i + 1;
        };
        postcond: assert sum <= N * max;
    }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES sum, max, i, pc

vars == << sum, max, i, pc >>

Init == (* Global variables *)
        /\ sum = 0
        /\ max = 0
        /\ i = defaultInitValue
        /\ pc = "precond"

precond == /\ pc = "precond"
           /\ Assert(N >= 0 /\ \A j \in 1..N : a[j] >= 0, "Failure of assertion at line 17, column 18.") 
           /\ pc' = "loopinit"
           /\ UNCHANGED << sum, max, i >>

loopinit == /\ pc = "loopinit"
            /\ i' = 1
            /\ pc' = "mainloop"
            /\ UNCHANGED << sum, max >>

mainloop == /\ pc = "mainloop"
            /\ IF i <= N
                  THEN /\ pc' = "testmax"
                  ELSE /\ pc' = "postcond"
            /\ UNCHANGED << sum, max, i >>

testmax == /\ pc = "testmax"
           /\ IF max < a[i]
                 THEN /\ pc' = "updatemax"
                 ELSE /\ pc' = "updatesum"
           /\ UNCHANGED << sum, max, i >>

updatemax == /\ pc = "updatemax"
             /\ max' = a[i]
             /\ pc' = "updatesum"
             /\ UNCHANGED << sum, i >>

updatesum == /\ pc = "updatesum"
             /\ sum' = sum + a[i]
             /\ pc' = "incloop"
             /\ UNCHANGED << max, i >>

incloop == /\ pc = "incloop"
           /\ i' = i + 1
           /\ pc' = "mainloop"
           /\ UNCHANGED << sum, max >>

postcond == /\ pc = "postcond"
            /\ Assert(sum <= N * max, 
                      "Failure of assertion at line 26, column 19.")
            /\ pc' = "Done"
            /\ UNCHANGED << sum, max, i >>

Next == precond \/ loopinit \/ mainloop \/ testmax \/ updatemax
           \/ updatesum \/ incloop \/ postcond
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

VscompPostCondition == (pc = "Done") => /\ sum <= N * max   \** property from original problem
                                        /\ sum = EltSum     \** more precise specification
                                        /\ max = Max
                                        
PositiveN == N >= 0
PositiveValues == \A j \in 1..N : a[j] >= 0
(***************************************************************************
PositiveN == N >= 0
PositiveValues == \forall j \in 1..N : a[j] >= 0
ASSUME PreCondition ==  PositiveN /\ PositiveValues
THEOREM VscompCorrectness == Spec => []VscompPostCondition
BY PreCondition DEF PositiveN, PositiveValues, Spec, VscompPostCondition
 ***************************************************************************)
TypesInv ==
    /\ sum \in Nat
    /\ max \in Nat
    /\ i \in 1..N+1 \union { defaultInitValue }
    /\ (pc \notin {"precond", "loopinit"}) => i \in Nat
    /\ pc \in {"precond", "loopinit", "mainloop", "testmax", "updatemax", "updatesum", "incloop", "postcond", "Done"}
    /\ \A j \in 1..N : a[j] \in Nat 
 
InductiveInvariant ==
        /\ sum + PartialSum[i] = EltSum
        /\ max = SubMax(i)
        /\ sum <= N * i
        
THEOREM Init => TypesInv
BY DEF Init, TypesInv

THEOREM Next /\ TypesInv => TypesInv'
<1> USE DEF TypesInv
<1>1. CASE precond
    BY <1>1 DEF precond
<1>2. CASE loopinit
    BY <1>2 DEF loopinit
<1>3. CASE mainloop
    BY <1>3 DEF mainloop
<1>4. CASE testmax
    BY <1>4 DEF testmax
<1>5. CASE updatemax
    BY <1>5 DEF updatemax
<1>6. CASE updatesum
    BY <1>6 DEF updatesum
<1>7. CASE incloop
    BY <1>7 DEF incloop
<1>8. CASE postcond
    BY <1>8 DEF postcond
<1>9. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8 DEF Next   
(*THEOREM Init => InductiveInvariant*)
(*BY DEF Init, InductiveInvariant, PartialSum, EltSum*)

THEOREM Next /\ InductiveInvariant => InductiveInvariant'
<1> USE DEF Next
<1>1. CASE pc = "precond"
<1>2. CASE pc = "loopinit"
<1>3. CASE pc = "mainloop"
<1>4. CASE pc = "testmax"
<1>5. CASE pc = "updatemax"
<1>6. CASE pc = "updatesum"
<1>7. CASE pc = "incloop"
<1>8. CASE pc = "postcond"
<1>9. QED

=============================================================================
\* Modification History
\* Last modified Tue Jul 12 14:12:15 CEST 2011 by loic
\* Last modified Fri Jul 08 19:09:36 CEST 2011 by merz
\* Created Thu Jul 07 15:44:48 CEST 2011 by loic
