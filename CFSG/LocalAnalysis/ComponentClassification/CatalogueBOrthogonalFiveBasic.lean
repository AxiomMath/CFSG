module

public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u

@[expose] def symplecticGram (K : Type u) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

@[expose] def selfAdjointSubmodule (K : Type u) [Field K] :
    Submodule K (Matrix (Fin 4) (Fin 4) K) where
  carrier := {X | Xᵀ * symplecticGram K = symplecticGram K * X ∧ X.trace = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX, htX⟩ ⟨hY, htY⟩
    constructor
    · simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, hX, hY]
    · rw [Matrix.trace_add, htX, htY, add_zero]
  smul_mem' := by
    rintro a X ⟨hX, htX⟩
    constructor
    · simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hX]
    · rw [Matrix.trace_smul, htX, smul_zero]

variable {K : Type u} [Field K]

theorem selfAdjoint_mem_iff (X : Matrix (Fin 4) (Fin 4) K) :
    X ∈ selfAdjointSubmodule K ↔
      Xᵀ * symplecticGram K = symplecticGram K * X ∧ X.trace = 0 := Iff.rfl

theorem selfAdjoint_entries (h2 : (2 : K) ≠ 0) (X : selfAdjointSubmodule K) :
    X.val = !![X.val 0 0, X.val 0 1, 0, X.val 0 3;
      X.val 1 0, -X.val 0 0, -X.val 0 3, 0;
      0, X.val 2 1, X.val 0 0, X.val 1 0;
      -X.val 2 1, 0, X.val 0 1, -X.val 0 0] := by
  have h (i j : Fin 4) := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M i j) X.property.1
  have h20 := h 0 0
  have h30 := h 0 1
  have h31 := h 1 1
  have h02 := h 2 2
  have h12 := h 2 3
  have h13 := h 3 3
  have h22 := h 0 2
  have h23 := h 0 3
  have h32 := h 1 2
  have h33 := h 1 3
  simp [symplecticGram, Matrix.mul_apply, Fin.sum_univ_four] at h20 h30 h31 h02 h12 h13 h22 h23 h32 h33
  have ht : X.val 0 0 + X.val 1 1 + X.val 2 2 + X.val 3 3 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_four, add_assoc] using X.property.2
  have hx20 : X.val 2 0 = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * X.val 2 0 = 0 by linear_combination -h20)).resolve_left h2
  have hx31 : X.val 3 1 = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * X.val 3 1 = 0 by linear_combination -h31)).resolve_left h2
  have hx02 : X.val 0 2 = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * X.val 0 2 = 0 by linear_combination h02)).resolve_left h2
  have hx13 : X.val 1 3 = 0 := by
    apply (mul_eq_zero.mp (show (2 : K) * X.val 1 3 = 0 by linear_combination h13)).resolve_left h2
  have hx11 : X.val 1 1 = -X.val 0 0 := by
    have hm : (2 : K) * (X.val 0 0 + X.val 1 1) = 0 := by
      linear_combination ht + h22 + h33
    have hz := (mul_eq_zero.mp hm).resolve_left h2
    linear_combination hz
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact hx02
  · rfl
  · rfl
  · exact hx11
  · exact h12
  · exact hx13
  · exact hx20
  · rfl
  · exact h22.symm
  · exact h23.symm
  · change X.val 3 0 = -X.val 2 1
    linear_combination -h30
  · exact hx31
  · exact h32.symm
  · exact h33.symm.trans hx11

@[expose] def selfAdjointCoordinates (h2 : (2 : K) ≠ 0) :
    (Fin 5 → K) ≃ₗ[K] selfAdjointSubmodule K where
  toFun x := ⟨!![x 0, x 1, 0, x 3; x 2, -x 0, -x 3, 0;
    0, x 4, x 0, x 2; -x 4, 0, x 1, -x 0], by
    constructor
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [symplecticGram, Matrix.mul_apply, Fin.sum_univ_four]
    · simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]⟩
  invFun X := ![X.val 0 0, X.val 0 1, X.val 1 0, X.val 0 3, X.val 2 1]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv X := Subtype.ext (selfAdjoint_entries h2 X).symm
  map_add' x y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact neg_add _ _ | exact (add_zero (0 : K)).symm
  map_smul' a x := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (smul_zero a).symm | exact (smul_neg a _).symm

theorem selfAdjointCoordinates_val (h2 : (2 : K) ≠ 0) (x : Fin 5 → K) :
    (selfAdjointCoordinates h2 x).val =
      !![x 0, x 1, 0, x 3; x 2, -x 0, -x 3, 0;
        0, x 4, x 0, x 2; -x 4, 0, x 1, -x 0] := rfl

theorem selfAdjoint_finrank (h2 : (2 : K) ≠ 0) :
    Module.finrank K (selfAdjointSubmodule K) = 5 := by
  rw [← (selfAdjointCoordinates h2).finrank_eq]
  simp

@[expose] def selfAdjointForm (K : Type u) [Field K] :
    QuadraticForm K (selfAdjointSubmodule K) :=
  let a := (Matrix.entryLinearMap K K (0 : Fin 4) 0).comp (selfAdjointSubmodule K).subtype
  let b := (Matrix.entryLinearMap K K (0 : Fin 4) 1).comp (selfAdjointSubmodule K).subtype
  let c := (Matrix.entryLinearMap K K (1 : Fin 4) 0).comp (selfAdjointSubmodule K).subtype
  let s := (Matrix.entryLinearMap K K (0 : Fin 4) 3).comp (selfAdjointSubmodule K).subtype
  let t := (Matrix.entryLinearMap K K (2 : Fin 4) 1).comp (selfAdjointSubmodule K).subtype
  linMulLin a a + linMulLin b c - linMulLin s t

theorem selfAdjointForm_apply (X : selfAdjointSubmodule K) :
    selfAdjointForm K X = X.val 0 0 * X.val 0 0 + X.val 0 1 * X.val 1 0 -
      X.val 0 3 * X.val 2 1 := rfl

theorem selfAdjointForm_polar (X Y : selfAdjointSubmodule K) :
    (selfAdjointForm K).polarBilin X Y =
      2 * X.val 0 0 * Y.val 0 0 + X.val 0 1 * Y.val 1 0 + X.val 1 0 * Y.val 0 1 -
        X.val 0 3 * Y.val 2 1 - X.val 2 1 * Y.val 0 3 := by
  rw [polarBilin_apply_apply, polar, selfAdjointForm_apply, selfAdjointForm_apply,
    selfAdjointForm_apply]
  change (X.val 0 0 + Y.val 0 0) * (X.val 0 0 + Y.val 0 0) +
    (X.val 0 1 + Y.val 0 1) * (X.val 1 0 + Y.val 1 0) -
    (X.val 0 3 + Y.val 0 3) * (X.val 2 1 + Y.val 2 1) -
    (X.val 0 0 * X.val 0 0 + X.val 0 1 * X.val 1 0 - X.val 0 3 * X.val 2 1) -
    (Y.val 0 0 * Y.val 0 0 + Y.val 0 1 * Y.val 1 0 - Y.val 0 3 * Y.val 2 1) = _
  ring

theorem selfAdjointForm_nondegenerate (h2 : (2 : K) ≠ 0) :
    (selfAdjointForm K).polarBilin.Nondegenerate := by
  have left : (selfAdjointForm K).polarBilin.SeparatingLeft := by
    intro X hX
    have h0 := hX (selfAdjointCoordinates h2 ![1, 0, 0, 0, 0])
    have h1 := hX (selfAdjointCoordinates h2 ![0, 0, 1, 0, 0])
    have h2' := hX (selfAdjointCoordinates h2 ![0, 1, 0, 0, 0])
    have h3 := hX (selfAdjointCoordinates h2 ![0, 0, 0, 0, 1])
    have h4 := hX (selfAdjointCoordinates h2 ![0, 0, 0, 1, 0])
    rw [selfAdjointForm_polar] at h0 h1 h2' h3 h4
    have hx0 : X.val 0 0 = 0 := by
      apply (mul_eq_zero.mp (show (2 : K) * X.val 0 0 = 0 by
        simpa [selfAdjointCoordinates] using h0)).resolve_left h2
    have hx1 : X.val 0 1 = 0 := by simpa [selfAdjointCoordinates] using h1
    have hx2 : X.val 1 0 = 0 := by simpa [selfAdjointCoordinates] using h2'
    have hx3 : X.val 0 3 = 0 := by simpa [selfAdjointCoordinates] using h3
    have hx4 : X.val 2 1 = 0 := by simpa [selfAdjointCoordinates] using h4
    apply Subtype.ext
    rw [selfAdjoint_entries h2 X, hx0, hx1, hx2, hx3, hx4]
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact neg_zero
  refine ⟨left, ?_⟩
  intro X hX
  apply left X
  intro Y
  rw [polarBilin_apply_apply, polar_comm]
  exact hX Y

theorem selfAdjoint_square (h2 : (2 : K) ≠ 0) (X : selfAdjointSubmodule K) :
    X.val * X.val = selfAdjointForm K X • (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [selfAdjointForm_apply, selfAdjoint_entries h2 X]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem selfAdjoint_anticommutator (h2 : (2 : K) ≠ 0)
    (X Y : selfAdjointSubmodule K) :
    X.val * Y.val + Y.val * X.val =
      (selfAdjointForm K).polarBilin X Y • (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [selfAdjointForm_polar, selfAdjoint_entries h2 X, selfAdjoint_entries h2 Y]
  ext i j
  simp_rw [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
