module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix

variable {F : Type} [Field F]

structure IsElemModScalars (p : ℕ) (A : Subgroup (GL (Fin 3) F)) : Prop where
  center_le : Subgroup.center (GL (Fin 3) F) ≤ A
  pow_mem : ∀ g ∈ A, g ^ p ∈ Subgroup.center (GL (Fin 3) F)
  commutator_mem : ∀ g ∈ A, ∀ h ∈ A, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center (GL (Fin 3) F)
  card_eq : Nat.card (A ⧸ (Subgroup.center (GL (Fin 3) F)).subgroupOf A) = p ^ 2

@[expose] def fixSetThree (p : ℕ) (A : Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F) :=
  {x | (x : Matrix (Fin 3) (Fin 3) F).det = 1 ∧ ¬ p ∣ orderOf x ∧
    ∃ g ∈ A, g ∉ Subgroup.center (GL (Fin 3) F) ∧ g * x = x * g}

@[expose] def diagThree (d : Fin 3 → Fˣ) : GL (Fin 3) F :=
  ⟨diagonal fun i => (d i : F), diagonal fun i => ((d i)⁻¹ : Fˣ), by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; simp⟩

@[expose] def diagOmega (ω : Fˣ) : GL (Fin 3) F := diagThree ![1, ω, ω ^ 2]

@[expose] def diagSign (i : Fin 3) : GL (Fin 3) F := diagThree fun j => if j = i then 1 else -1

@[expose] def cycMatrix (μ : F) : Matrix (Fin 3) (Fin 3) F := !![0, 0, μ; 1, 0, 0; 0, 1, 0]

@[expose] def cycMat (μ : Fˣ) : GL (Fin 3) F :=
  ⟨cycMatrix μ, !![0, 1, 0; 0, 0, 1; ((μ⁻¹ : Fˣ) : F), 0, 0], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [cycMatrix, Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [cycMatrix, Matrix.mul_apply, Fin.sum_univ_three]⟩

@[expose] def fourierMat (ω : F) (k : Fin 3) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => 2 / 3 * ω ^ (k.val * (i - j).val) - if i = j then 1 else 0

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
