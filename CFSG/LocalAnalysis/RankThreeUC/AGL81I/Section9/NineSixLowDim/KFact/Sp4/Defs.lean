module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

variable {F : Type} [Field F]

structure IsElemSp (p : ℕ) (E : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) : Prop where
  le_sp : E ≤ CFSG.Open.StatedSp 2 F
  comm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g
  pow_eq_one : ∀ g ∈ E, g ^ p = 1
  card_eq : Nat.card E = p ^ 2

@[expose] def fixSetSp (p : ℕ) (E : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) :
    Set (GL (Fin 2 ⊕ Fin 2) F) :=
  {x | x ∈ CFSG.Open.StatedSp 2 F ∧ ¬ p ∣ orderOf x ∧ ∃ g ∈ E, g ≠ 1 ∧ g * x = x * g}

@[expose] def spDiagMatrix (a b : F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  diagonal (Sum.elim ![a, b] ![a⁻¹, b⁻¹])

@[expose] def spIdx : Fin 2 ⊕ Fin 2 → Fin 2 × Fin 2 :=
  Sum.elim (fun i => (i, 0)) (fun i => (i, 1))

@[expose] def spPairMatrix (s t : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun x y =>
    if (spIdx x).1 = (spIdx y).1 then ![s, t] (spIdx x).1 (spIdx x).2 (spIdx y).2 else 0

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
