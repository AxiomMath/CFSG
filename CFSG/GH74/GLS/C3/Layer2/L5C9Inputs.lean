
module

public import CFSG.GH74.GLS.C3.Layer2.L5C0Base
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0Base

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5.HF

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
@[expose] def IsLin16 (m : Perm (Fin 16)) : Prop := ∀ i j, m (xor16 i j) = xor16 (m i) (m j)

@[expose] def linFun (q : Fin 16 × Fin 16 × Fin 16 × Fin 16) (i : Fin 16) : Fin 16 :=
  xor16 (xor16 (if i.val % 2 = 1 then q.1 else 0) (if i.val / 2 % 2 = 1 then q.2.1 else 0))
    (xor16 (if i.val / 4 % 2 = 1 then q.2.2.1 else 0) (if i.val / 8 % 2 = 1 then q.2.2.2 else 0))

@[expose] def invTab (f : Fin 16 → Fin 16) (j : Fin 16) : Fin 16 :=
  ((List.finRange 16).find? fun i => decide (f i = j)).getD 0

@[expose] def isPermChk (f : Fin 16 → Fin 16) : Bool :=
  (List.finRange 16).all fun i => decide (invTab f (f i) = i) && decide (f (invTab f i) = i)

@[expose] def mkPerm (f : Fin 16 → Fin 16) : Perm (Fin 16) :=
  if h : isPermChk f = true then
    { toFun := f
      invFun := invTab f
      left_inv := fun i => by
        simp only [isPermChk, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
          decide_eq_true_eq, true_implies] at h
        exact (h i).1
      right_inv := fun i => by
        simp only [isPermChk, List.all_eq_true, List.mem_finRange, Bool.and_eq_true,
          decide_eq_true_eq, true_implies] at h
        exact (h i).2 }
  else 1

@[expose] def allQ2 (g : Fin 16 → Fin 16 → Bool) (c : Perm (Fin 16) → Bool) : Bool :=
  (List.finRange 16).all fun a => (List.finRange 16).all fun b => !(g a b) ||
    (List.finRange 16).all fun c' => (List.finRange 16).all fun d =>
      !(isPermChk (linFun (a, b, c', d))) || c (mkPerm (linFun (a, b, c', d)))

@[expose] def Ppl : Finset (Fin 16) := {0, 4, 8, 12}

@[expose] def Qpl : Finset (Fin 16) := {0, 1, 2, 3}

@[expose] def fam0 : Finset (Finset (Fin 16)) :=
  {{0, 5, 11, 14}, {0, 7, 10, 13}, {0, 1, 2, 3}, {0, 6, 9, 15}}

@[expose] def fam1 : Finset (Finset (Fin 16)) :=
  {{0, 6, 11, 13}, {0, 7, 9, 14}, {0, 5, 10, 15}, {0, 1, 2, 3}}

@[expose] def twPerm : Perm (Fin 16) :=
  List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [10, 11] * List.formPerm [14, 15]

@[expose] def linChk (m : Perm (Fin 16)) : Bool :=
  (List.finRange 16).all fun i => (List.finRange 16).all fun j =>
    decide (m (xor16 i j) = xor16 (m i) (m j))

@[expose] def gTw : Amb 5 := (1, swap 0 1)

@[expose] def tabL (p : Perm (Fin 16)) : List (Fin 16) := (List.finRange 16).map p

@[expose] def tmulL (a b : List (Fin 16)) : List (Fin 16) := b.map fun j => a.getD j.val 0

@[expose] def closureL (gens : List (List (Fin 16))) (k : ℕ) : List (List (Fin 16)) :=
  (fun l => (l ++ l.flatMap fun g => gens.map (tmulL g ·)).dedup)^[k] [List.finRange 16]

@[expose] def orbStep (gs : List (Perm (Fin 16))) (l : List (Finset (Fin 16))) :
    List (Finset (Fin 16)) :=
  ((l ++ l.flatMap fun V => gs.map fun g => V.image g).dedup).take 5

@[expose] def orbList (gs : List (Perm (Fin 16))) (k : ℕ) : List (Finset (Fin 16)) :=
  (orbStep gs)^[k] [Qpl]

@[expose] def n24Pre (m : Perm (Fin 16)) : Bool :=
  decide (Qpl.image m ≠ Qpl) && decide (Qpl.image m ∩ Qpl = {0}) &&
    decide (Qpl.image m ∩ Ppl = {0})

@[expose] def gN (a b : Fin 16) : Bool :=
  decide (({0, a, b, xor16 a b} : Finset (Fin 16)) ≠ Qpl) &&
    decide (({0, a, b, xor16 a b} : Finset (Fin 16)) ∩ Qpl = {0}) &&
    decide (({0, a, b, xor16 a b} : Finset (Fin 16)) ∩ Ppl = {0})

@[expose] def n24Cov (C : List (List (Fin 16))) (tw : Bool) : Bool :=
  n24L.all fun A => decide (tabL (if tw then twPerm * A * twPerm⁻¹ else A) ∈ C)

@[expose] def n24Tail (m : Perm (Fin 16)) (o : Finset (Finset (Fin 16))) : Bool :=
  decide (Ppl.image m = Ppl) &&
    (let C := closureL ([yHat, wHat, m].map tabL) 8
     (decide (fam0 ⊆ o) && n24Cov C false) || (decide (fam1 ⊆ o) && n24Cov C true))

@[expose] def n24Chk (m : Perm (Fin 16)) : Bool :=
  let o := (orbList [yHat, wHat, m] 6).toFinset
  decide (5 ≤ o.card) || n24Tail m o

@[expose] def n24Entry (m : Perm (Fin 16)) : Bool := !(n24Pre m) || n24Chk m

@[expose] def planes0 : List (List (Fin 16)) :=
  [[0, 5, 11, 14], [0, 7, 10, 13], [0, 1, 2, 3], [0, 6, 9, 15]]

@[expose] def planes1 : List (List (Fin 16)) :=
  [[0, 6, 11, 13], [0, 7, 9, 14], [0, 5, 10, 15], [0, 1, 2, 3]]

@[expose] def fam0ChkL (m : Perm (Fin 16)) : Bool :=
  planes0.all fun V => planes0.any fun W => V.all fun x => decide (m x ∈ W)

@[expose] def fam1ChkL (m : Perm (Fin 16)) : Bool :=
  planes1.all fun V => planes1.any fun W => V.all fun x => decide (m x ∈ W)

@[expose] def gFam (a b : Fin 16) : Bool :=
  decide (({0, a, b, xor16 a b} : Finset (Fin 16)) ∈ fam0) ||
    decide (({0, a, b, xor16 a b} : Finset (Fin 16)) ∈ fam1)

@[expose] def presChk (f0 f1 : Bool) (m : Perm (Fin 16)) : Bool :=
  !(f0 || f1) || decide (Ppl.image m = Ppl)

@[expose] def G72gens : List (Perm (Fin 16)) := [yHat, wHat, n24L.getD 6 1, cHat]

@[expose] def permOfTab (t : List (Fin 16)) : Perm (Fin 16) := mkPerm fun i => t.getD i.val 0

@[expose] def G72L : List (Perm (Fin 16)) := (closureL (G72gens.map tabL) 8).map permOfTab

@[expose] def fam0Chk (m : Perm (Fin 16)) : Bool := decide (∀ V ∈ fam0, V.image m ∈ fam0)

@[expose] def cHatChk (f0 : Bool) (m : Perm (Fin 16)) : Bool :=
  !f0 || decide (m ∈ n24L) ||
    decide (tabL cHat ∈ closureL ([wHat, n24L.getD 6 1, m].map tabL) 8)

@[expose] def famEntry (G : List (Perm (Fin 16))) (m : Perm (Fin 16)) : Bool :=
  let f0 := fam0ChkL m
  let f1 := fam1ChkL m
  presChk f0 f1 m && (!f0 || decide (m ∈ G)) && cHatChk f0 m

@[expose] def d8Chk (b c : Perm (Fin 16)) : Bool :=
  let gens : List (Perm (Fin 16)) := [yHat, b, c]
  let T := closureL (gens.map tabL) 8
  (T.all fun t => gens.all fun s =>
      decide (tmulL t (tabL s) ∈ T) && decide (tmulL t (tabL s⁻¹) ∈ T)) &&
    (let L := n24L.filter fun x => decide (tabL x ∈ T)
     !decide (L.length = 8) || (L.all (fun x => decide (x ∈ d8L)) && d8L.all fun x => decide (x ∈ L)))

end CFSG.GH74.GLS.C3.Layer2.L5.HF
