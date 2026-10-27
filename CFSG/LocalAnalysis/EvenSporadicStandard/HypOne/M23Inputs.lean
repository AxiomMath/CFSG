module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.FourCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Check

public section

namespace CFSG.EvenSporadicStandard.HypOne.M23

open CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native

@[expose] def gens : List (Equiv.Perm (Fin 23)) := [m23PermA, m23PermB]

@[expose] def centGens1 : List (Equiv.Perm (Fin 23)) := m23CentWords1.map (evalCodes gens)

@[expose] def fourWords1 : List (List ℤ) :=
  [[-2, 4, -3, -1, -2, 4, -2, 4, 3, 3], [-1, 4, 3, 3, 4, 1, -4, 3, 4, 1], [4, 3, 3, 4, 4, 2]]

@[expose] def wordE1 : List ℤ :=
  [2, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2,
    -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2,
    -1, -2, -1, 2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2,
    2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1]

@[expose] def wordE2 : List ℤ :=
  [2, 1, -2, 1, 2, 2, 1, -2, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -1, 2,
    -1, 2, -1, -2, -1, -2, -1, -2, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -2, -1, -2, -2, -2, -2,
    -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -2,
    -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, -1, 2, -1, 2]

@[expose] def wordE3 : List ℤ :=
  [-2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1,
    2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, -1, -2, -1,
    -2, -2, -1, -2, -1, -2, -2, -1, -2]

@[expose] def e1 : Equiv.Perm (Fin 23) := evalCodes gens wordE1

@[expose] def e2 : Equiv.Perm (Fin 23) := evalCodes gens wordE2

@[expose] def e3 : Equiv.Perm (Fin 23) := evalCodes gens wordE3

@[expose] def fourData : Bool := fourCheck 23 m23CentQ1 centGens1 fourWords1 4000

@[expose] def e8Data : Bool := e8Check 23 (toTable e1) (toTable e2) (toTable e3)

end CFSG.EvenSporadicStandard.HypOne.M23
