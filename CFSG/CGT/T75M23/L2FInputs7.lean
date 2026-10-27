module

public import CFSG.CGT.T75M23.N7ModelInputs

public section

namespace CFSG.CGT.T75M23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

abbrev Word6 : Type := List (Fin 6 × Bool)

@[expose] def tw7 (k : ℕ) : Word6 :=
  (List.finRange 4).flatMap fun i => if k.testBit i.val then [(Fin.natAdd 2 i, true)] else []

@[expose] def bGen7 : Fin 2 → Word6 :=
  ![[(1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true)],
   [(1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
    (1, true), (0, true), (1, true)]]

@[expose] def dThetaTwo7 : Fin 3 → Word6 :=
  ![[(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
    (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true),
    (1, true), (0, true), (1, true), (2, true), (3, true), (4, true), (5, true)],
   [(0, true), (1, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true),
    (3, true), (4, true)],
   [(1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true),
    (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
    (1, true), (2, true), (5, true)]]

@[expose] def d0Two7 : Word6 :=
  [(0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (1, true), (1, true),
    (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true),
    (2, true), (5, true)]

@[expose] def d0W7 : Fin 2 → Word6 := ![[], d0Two7]

@[expose] def thetaW7 : Fin 2 → Fin 3 → Word6 := ![dTheta7, dThetaTwo7]

@[expose] def tConj7 (x xi t : Table) : Table := compT 23 (compT 23 x t) xi

@[expose] def commTab7 (x t : Table) : Bool := compT 23 x t == compT 23 t x

@[expose] def tTabs7 : List Table := (List.range 16).map fun k => n7Tab (tw7 k)

@[expose] def bt0 : Table := n7Tab (bGen7 0)

@[expose] def bt1 : Table := n7Tab (bGen7 1)

@[expose] def bt01 : Table := n7Tab (bGen7 0 ++ bGen7 1)

@[expose] def bTabs7 : List Table := [idT 23, bt0, bt1, bt01]

@[expose] def normL7 (L : List Table) (p q X Xi : Table) : Bool :=
  L.contains (tConj7 X Xi p) && L.contains (tConj7 X Xi q) && L.contains (tConj7 Xi X p) &&
    L.contains (tConj7 Xi X q)

@[expose] def normB7 (X Xi : Table) : Bool := normL7 bTabs7 bt0 bt1 X Xi

@[expose] def tCheck7 : Bool :=
  (List.range 16).all (fun k => (List.range 16).all fun l =>
    n7Tab (tw7 k ++ tw7 l) == n7Tab (tw7 (k ^^^ l))) &&
    (List.range 16).all fun k => (List.range 16).all fun l =>
      !(n7Tab (tw7 k) == n7Tab (tw7 l)) || k == l

@[expose] def bCheck7 : Bool :=
  compT 23 bt0 bt0 == idT 23 && compT 23 bt1 bt1 == idT 23 && commTab7 bt0 bt1 &&
    !(bt0 == idT 23) && !(bt1 == idT 23) && !(bt0 == bt1) && !(bt01 == idT 23) &&
    !(bt01 == bt0) && !(bt01 == bt1) && !(tTabs7.contains bt0)

@[expose] def genTab7 (k : ℕ) (b : Bool) : Table := n7Tab [(Fin.ofNat 6 k, b)]

@[expose] def normalCheck7 : Bool :=
  (List.range 6).all fun k => tTabs7.all fun t =>
    tTabs7.contains (tConj7 (genTab7 k true) (genTab7 k false) t) &&
      tTabs7.contains (tConj7 (genTab7 k false) (genTab7 k true) t)

@[expose] def dEvalW7 (w : List (Fin 3)) : Word6 := (w.map dGen7).flatten

@[expose] def aWords7 : List (List (Fin 3)) :=
  [[1, 2, 1, 2], [2, 1, 2, 1], [2, 1, 2, 2, 1, 2]]

@[expose] def bWords7 : List (List (Fin 3)) :=
  [[0, 1, 2, 2, 1, 0, 2], [1, 0, 2, 0, 1, 2, 2], [0, 1, 2, 1, 0, 2, 2]]

@[expose] def thWords7 : Fin 2 → Fin 3 → List (Fin 3) :=
  ![![[0], [0, 2, 2, 0, 1, 0, 2, 0], [2, 2]], ![[1, 0, 2, 0, 2, 2], [0, 2, 1, 2, 2, 1, 2],
    [0, 1, 2, 0, 1]]]

@[expose] def dRels7 : List (List (Fin 3)) :=
  [[0, 1, 0, 1, 0, 1], [2, 1, 0, 2, 1, 0, 2, 1, 0], [1, 2, 2, 1, 0, 2, 1, 2, 1, 0, 2, 2],
    [0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2], [1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2]]

@[expose] def evalT7 (u : Fin 3 → Table) (w : List (Fin 3)) : Table :=
  w.foldl (fun acc k => compT 23 acc (u k)) (idT 23)

@[expose] def tdd7 (i : Fin 3) : Table := n7Tab (dGen7 i)

@[expose] def tth7 (k : Fin 2) (i : Fin 3) : Table := n7Tab (thetaW7 k i)

@[expose] def td0_7 (k : Fin 2) : Table := n7Tab (d0W7 k)

@[expose] def dMemCheck7 : Bool :=
  (List.finRange 3).all (fun i => normB7 (tdd7 i) (n7Tab (invWord7 (dGen7 i)))) &&
    (List.finRange 2).all (fun k => (List.finRange 3).all fun i =>
      normB7 (tth7 k i) (n7Tab (invWord7 (thetaW7 k i)))) &&
    (List.finRange 2).all fun k => normB7 (td0_7 k) (n7Tab (invWord7 (d0W7 k)))

@[expose] def dRelCheck7 : Bool :=
  evalT7 tdd7 [0, 0] == idT 23 && evalT7 tdd7 [1, 1] == idT 23 &&
    evalT7 tdd7 [2, 2, 2] == idT 23 && dRels7.all fun w => evalT7 tdd7 w == idT 23

@[expose] def abWordsCheck7 : Bool :=
  aWords7.all (fun w => normB7 (n7Tab (dEvalW7 w)) (n7Tab (invWord7 (dEvalW7 w))) &&
      tTabs7.contains (evalT7 tdd7 w) && !(evalT7 tdd7 w == idT 23)) &&
    bWords7.all fun w => bTabs7.contains (evalT7 tdd7 w) && !(evalT7 tdd7 w == idT 23)

@[expose] def thetaSqCheck7 : Bool :=
  (List.finRange 2).all fun k => (List.finRange 3).all fun i =>
    evalT7 tdd7 (thWords7 k i) == tth7 k i &&
      evalT7 (tth7 k) (thWords7 k i) ==
        tConj7 (td0_7 k) (n7Tab (invWord7 (d0W7 k))) (tdd7 i)

end CFSG.CGT.T75M23
