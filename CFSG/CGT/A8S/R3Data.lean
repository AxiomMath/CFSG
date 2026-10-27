module

public import CFSG.CGT.A8S.N0Aff
public import CFSG.CGT.A8S.N0Words

public section

namespace CFSG.CGT.A8S.R3

open N0

@[expose] def projW5 (w : A8Word) : List (Fin 5 × Bool) :=
  w.map fun p => (Fin.ofNat 5 p.1.val, p.2)

@[expose] def dW (i : Fin 2) : List (Fin 5 × Bool) := projW5 (dWordA8 i)

@[expose] def thW (i : Fin 2) : List (Fin 5 × Bool) := projW5 (thetaWordA8 i)

@[expose] def nW : List (Fin 5 × Bool) := projW5 nWordA8

@[expose] def wW : List (Fin 5 × Bool) := projW5 wWordA8

@[expose] def yW (j : Fin 3) : List (Fin 5 × Bool) := projW5 (yWordA8 j)

@[expose] def fW (j : Fin 3) : List (Fin 5 × Bool) := projW5 (fWordA8 j)

@[expose] def wrongW (k : Fin 7) : List (Fin 5 × Bool) := projW5 (wrongWordA8 k)

theorem liftW5_dW : ∀ i, liftW5 (dW i) = dWordA8 i := by decide

theorem liftW5_thW : ∀ i, liftW5 (thW i) = thetaWordA8 i := by decide

theorem liftW5_nW : liftW5 nW = nWordA8 := by decide

theorem liftW5_wW : liftW5 wW = wWordA8 := by decide

theorem liftW5_wrongW : ∀ k, liftW5 (wrongW k) = wrongWordA8 k := by decide

@[expose] def dExp : List (Fin 2 × Bool) → List (Fin 5 × Bool)
  | [] => []
  | p :: v => (if p.2 then dW p.1 else FreeGroup.invRev (dW p.1)) ++ dExp v

@[expose] def thExp : List (Fin 2 × Bool) → List (Fin 5 × Bool)
  | [] => []
  | p :: v => (if p.2 then thW p.1 else FreeGroup.invRev (thW p.1)) ++ thExp v

@[expose] def uD : List (Fin 2 × Bool) :=
  [(0, true), (1, true), (0, false), (1, false), (0, true), (1, false)]

@[expose] def bD : List (Fin 2 × Bool) := [(0, true), (1, true), (1, true), (0, false)]

@[expose] def yD : Fin 3 → List (Fin 2 × Bool) :=
  ![[(1, true), (0, false), (1, false), (0, true), (1, true)],
    [(1, true), (0, false), (1, true), (0, true), (1, true)],
    [(0, true), (1, true), (0, false), (1, true), (1, true)]]

@[expose] def aD : Fin 3 → List (Fin 2 × Bool) :=
  ![[(0, true), (1, true), (1, true), (0, false), (1, false)],
    [(0, true), (1, true), (0, false), (1, false), (0, true), (1, true)],
    [(1, true), (1, true)]]

@[expose] def bbD : Fin 3 → List (Fin 2 × Bool) :=
  ![[(0, true), (1, true), (0, false), (1, true), (1, true)],
    [(1, true), (0, true), (1, true), (0, true)],
    [(0, false), (1, true), (0, false), (1, true)]]

@[expose] def affBEq (p q : ℕ × Cols3) : Bool :=
  natEqB p.1 q.1 && natEqB p.2.c0 q.2.c0 && natEqB p.2.c1 q.2.c1 && natEqB p.2.c2 q.2.c2

theorem eq_of_affBEq {p q : ℕ × Cols3} (h : affBEq p q = true) : p = q := by
  simp only [affBEq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact Prod.ext (eq_of_natEqB h1)
    (Cols3.ext (eq_of_natEqB h2) (eq_of_natEqB h3) (eq_of_natEqB h4))

theorem affBEq_self (p : ℕ × Cols3) : affBEq p p = true := by
  simp [affBEq, natEqB]

theorem affEval_thExp_uD : affBEq (affEval (thExp uD)) (affEval (dExp uD)) = true := by
  decide +kernel

theorem affEval_conj_uD :
    affBEq (affEval (nW ++ dExp uD ++ FreeGroup.invRev nW)) (affEval (dExp bD)) = true := by
  decide +kernel

theorem affEval_thExp_bD : affBEq (affEval (thExp bD)) (affEval [(2, true)]) = true := by
  decide +kernel

theorem affEval_t0_ne : affBEq (affEval [(2, true)]) (affEval []) = false := by decide +kernel

theorem affEval_yD : ∀ j, affBEq (affEval (yW j)) (affEval (dExp (yD j))) = true := by
  decide +kernel

theorem affEval_aD : ∀ j, affBEq (affEval (FreeGroup.invRev nW ++ thExp (yD j) ++ nW))
    (affEval (dExp (aD j))) = true := by
  decide +kernel

theorem affEval_bbD : ∀ j, affBEq (affEval (nW ++ thExp (aD j) ++ FreeGroup.invRev nW))
    (affEval (dExp (bbD j))) = true := by
  decide +kernel

theorem affEval_fW : ∀ j, affBEq (affEval (thExp (bbD j))) (affEval (fW j)) = true := by
  decide +kernel

@[expose] def affMul (p q : ℕ × Cols3) : ℕ × Cols3 :=
  (p.1 ^^^ applyC3 p.2 q.1, compC3 p.2 q.2)

@[expose] def inWAff (X : ℕ × Cols3) : Bool :=
  (List.finRange 3).all fun j => affBEq (affMul (affEval (yW j)) X) (affMul X (affEval (fW j)))

@[expose] def candAff (X : ℕ × Cols3) : Bool :=
  affBEq X (affEval wW) || (List.finRange 7).any fun k => affBEq X (affEval (wrongW k))

@[expose] def wCheck : Bool :=
  wordCodes.all fun c => !inWAff (affEval (wordOfCode c)) || candAff (affEval (wordOfCode c))

end CFSG.CGT.A8S.R3
