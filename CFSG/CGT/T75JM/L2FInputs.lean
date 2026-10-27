module

public import CFSG.CGT.T75JM.N0ModelInputs

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

abbrev W6 : Type := List (Fin 6 × Bool)

@[expose] def tw (k : ℕ) : W6 :=
  (List.finRange 4).flatMap fun i => if k.testBit i.val then [(Fin.natAdd 2 i, true)] else []

@[expose] def tConj (x xi t : Table) : Table := compT 22 (compT 22 x t) xi

@[expose] def commTab (x t : Table) : Bool := compT 22 x t == compT 22 t x

@[expose] def tTabs : List Table := (List.range 16).map fun k => n0Tab (tw k)

@[expose] def tb0 : Table := n0Tab (bGen 0)

@[expose] def tb1 : Table := n0Tab (bGen 1)

@[expose] def tb01 : Table := n0Tab (bGen 0 ++ bGen 1)

@[expose] def bTabs : List Table := [idT 22, tb0, tb1, tb01]

@[expose] def normL (L : List Table) (p q X Xi : Table) : Bool :=
  L.contains (tConj X Xi p) && L.contains (tConj X Xi q) && L.contains (tConj Xi X p) &&
    L.contains (tConj Xi X q)

@[expose] def normB (X Xi : Table) : Bool := normL bTabs tb0 tb1 X Xi

@[expose] def tCheck : Bool :=
  (List.range 16).all (fun k => (List.range 16).all fun l =>
    n0Tab (tw k ++ tw l) == n0Tab (tw (k ^^^ l))) &&
    (List.range 16).all fun k => (List.range 16).all fun l =>
      !(n0Tab (tw k) == n0Tab (tw l)) || k == l

@[expose] def bCheck : Bool :=
  compT 22 tb0 tb0 == idT 22 && compT 22 tb1 tb1 == idT 22 && commTab tb0 tb1 &&
    !(tb0 == idT 22) && !(tb1 == idT 22) && !(tb0 == tb1) && !(tb01 == idT 22) &&
    !(tb01 == tb0) && !(tb01 == tb1) && !(tTabs.contains tb0)

@[expose] def alphaImg : Fin 6 → W6 := fun i =>
  match i with
  | 0 => [(0, true), (1, true), (1, true), (0, true)]
  | 1 => [(1, true), (2, true)]
  | 2 => [(3, true), (4, true)]
  | 3 => [(2, true), (3, true)]
  | 4 => [(3, true), (4, true), (5, true)]
  | 5 => [(3, true)]

@[expose] def substWord (w : W6) : W6 :=
  w.flatMap fun p => if p.2 then alphaImg p.1 else invWord (alphaImg p.1)

@[expose] def alphaRelCheck : Bool := rels6.all fun r => n0Tab (substWord r) == idT 22

@[expose] def alphaTCheck : Bool :=
  (List.range 16).all fun k => tTabs.contains (n0Tab (substWord (tw k)))

@[expose] def dEvalW (w : List (Fin 2)) : W6 := (w.map dGen).flatten

@[expose] def thEvalW (w : List (Fin 2)) : W6 := (w.map dTheta).flatten

@[expose] def aWords : List (List (Fin 2)) :=
  [[0, 0, 0, 1, 1, 0, 1, 1], [1, 1], [0, 0, 0, 1, 1, 0]]

@[expose] def bWords : List (List (Fin 2)) :=
  [[0, 0, 1, 0, 0, 1, 1, 1], [0, 0], [1, 0, 0, 1, 1, 1]]

@[expose] def thWords : Fin 2 → List (Fin 2) := fun i =>
  match i with
  | 0 => [1, 0, 0, 1, 0]
  | 1 => [1, 1, 0, 1, 0]

@[expose] def evalT (u : Fin 2 → Table) (w : List (Fin 2)) : Table :=
  w.foldl (fun acc k => compT 22 acc (u k)) (idT 22)

@[expose] def tdd (i : Fin 2) : Table := n0Tab (dGen i)

@[expose] def tth (i : Fin 2) : Table := n0Tab (dTheta i)

@[expose] def dMemCheck : Bool :=
  normB (tdd 0) (n0Tab (invWord (dGen 0))) && normB (tdd 1) (n0Tab (invWord (dGen 1))) &&
    normB (tth 0) (n0Tab (invWord (dTheta 0))) && normB (tth 1) (n0Tab (invWord (dTheta 1)))

@[expose] def dRelCheck : Bool :=
  evalT tdd [0, 0, 0, 0] == idT 22 && evalT tdd [1, 1, 1, 1] == idT 22 &&
    evalT tdd [0, 1, 0, 1, 0, 1] == idT 22

@[expose] def abWordsCheck : Bool :=
  aWords.all (fun w => normB (n0Tab (dEvalW w)) (n0Tab (invWord (dEvalW w))) &&
      tTabs.contains (evalT tdd w) && !(evalT tdd w == idT 22)) &&
    bWords.all fun w => bTabs.contains (evalT tdd w) && !(evalT tdd w == idT 22)

@[expose] def thetaSqCheck : Bool :=
  (List.finRange 2).all fun i =>
    evalT tdd (thWords i) == tth i && evalT tth (thWords i) == tdd i

end CFSG.CGT.T75JM
