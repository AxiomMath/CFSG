module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1Q8

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

abbrev V4 := Fin 4 → ZMod 2

@[expose] def acoord (σ : Equiv.Perm (Fin 5)) : ZMod 2 := if σ 0 = 1 ∨ σ 0 = 3 then 1 else 0

@[expose] def bcoord (σ : Equiv.Perm (Fin 5)) : ZMod 2 := if σ 0 = 2 ∨ σ 0 = 3 then 1 else 0

@[expose] def thRaw (r : RP) : V4 := ![acoord r.2, r.1 2 + r.1 3, bcoord r.2, r.1 1 + r.1 3]

@[expose] def vsel (a b : ZMod 2) : Equiv.Perm (Fin 5) :=
  if a = 0 ∧ b = 0 then 1 else if a = 1 ∧ b = 0 then s1 else if a = 0 ∧ b = 1 then sc else s3

@[expose] def preraw (v : V4) : RP := (![v 3 + v 1, v 3, v 1, 0, 0], vsel (v 0) (v 2))

@[expose] def gt1 : RP := (w04, 1)

@[expose] def gs01 : RP := (0, sa)

@[expose] def gk : RP := (0, c3)

@[expose] def gkinv : RP := (0, c3 * c3)

@[expose] def Mt1 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 1, 0, 0, 1]

@[expose] def Ms01 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 1, 0, 1]

@[expose] def Mk : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 1]

@[expose] def inW0 (v : V4) : Prop := v 0 = 0 ∧ v 2 = 0

instance : DecidablePred inW0 := fun v => by unfold inW0; infer_instance

@[expose] def inSing (v : V4) : Prop := quadHyp v = 0 ∧ v ≠ 0

instance : DecidablePred inSing := fun v => by unfold inSing; infer_instance

@[expose] def sing6 : Finset V4 := Finset.univ.filter fun v : V4 => inSing v ∧ ¬ inW0 v

@[expose] def gact (i : Fin 3) (v : V4) : V4 :=
  match i with
  | 0 => Mt1.mulVec v
  | 1 => Ms01.mulVec v
  | 2 => Mk.mulVec v

@[expose] def wact : List (Fin 3) → V4 → V4
  | [], v => v
  | i :: w, v => gact i (wact w v)

@[expose] def wordsUpTo : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => [] :: (wordsUpTo n).flatMap (fun w => (List.finRange 3).map (fun i => i :: w))

abbrev O4Cols :=
  Σ c0 : {c : V4 // quadHyp c = 0},
  Σ c1 : {c : V4 // quadHyp c = 0 ∧ quadHyp (c0.1 + c) = 1},
  Σ c2 : {c : V4 // quadHyp c = 0 ∧ quadHyp (c0.1 + c) = 0 ∧ quadHyp (c1.1 + c) = 0},
  {c : V4 // quadHyp c = 0 ∧ quadHyp (c0.1 + c) = 0 ∧ quadHyp (c1.1 + c) = 0 ∧
    quadHyp (c2.1 + c) = 1}

end CFSG.QuasithinUnique.A5
