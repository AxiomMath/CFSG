module

public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix QuadraticMap

universe u

@[expose] def traceZeroSubmodule (K : Type u) [Field K] :
    Submodule K (Matrix (Fin 2) (Fin 2) K) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 2) K K)

variable {K : Type u} [Field K]

theorem traceZero_diagonal (X : traceZeroSubmodule K) : X.val 1 1 = -X.val 0 0 := by
  have h : X.val 0 0 + X.val 1 1 = 0 := by
    have hx := X.property
    change X.val.trace = 0 at hx
    simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using hx
  linear_combination h

@[expose] def traceZeroCoordinates (K : Type u) [Field K] :
    (Fin 3 → K) ≃ₗ[K] traceZeroSubmodule K where
  toFun x := ⟨!![x 0, x 1; x 2, -x 0], by
    change (!![x 0, x 1; x 2, -x 0] : Matrix (Fin 2) (Fin 2) K).trace = 0
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]⟩
  invFun X := ![X.val 0 0, X.val 0 1, X.val 1 0]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv X := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · rfl
    · exact (traceZero_diagonal X).symm
  map_add' x y := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' a x := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem traceZeroCoordinates_val (x : Fin 3 → K) :
    (traceZeroCoordinates K x).val = !![x 0, x 1; x 2, -x 0] := rfl

theorem traceZero_finrank : Module.finrank K (traceZeroSubmodule K) = 3 := by
  rw [← (traceZeroCoordinates K).finrank_eq]
  simp

@[expose] def traceZeroForm (K : Type u) [Field K] :
    QuadraticForm K (traceZeroSubmodule K) :=
  let a := (Matrix.entryLinearMap K K (0 : Fin 2) 0).comp (traceZeroSubmodule K).subtype
  let b := (Matrix.entryLinearMap K K (0 : Fin 2) 1).comp (traceZeroSubmodule K).subtype
  let c := (Matrix.entryLinearMap K K (1 : Fin 2) 0).comp (traceZeroSubmodule K).subtype
  linMulLin a a + linMulLin b c

theorem traceZeroForm_apply (X : traceZeroSubmodule K) :
    traceZeroForm K X = X.val 0 0 * X.val 0 0 + X.val 0 1 * X.val 1 0 := rfl

theorem traceZeroForm_eq_neg_det (X : traceZeroSubmodule K) :
    traceZeroForm K X = -X.val.det := by
  rw [traceZeroForm_apply, Matrix.det_fin_two, traceZero_diagonal]
  ring

theorem traceZeroForm_polar (X Y : traceZeroSubmodule K) :
    (traceZeroForm K).polarBilin X Y =
      2 * X.val 0 0 * Y.val 0 0 + X.val 0 1 * Y.val 1 0 +
        X.val 1 0 * Y.val 0 1 := by
  rw [polarBilin_apply_apply, polar, traceZeroForm_apply, traceZeroForm_apply,
    traceZeroForm_apply]
  change (X.val 0 0 + Y.val 0 0) * (X.val 0 0 + Y.val 0 0) +
      (X.val 0 1 + Y.val 0 1) * (X.val 1 0 + Y.val 1 0) -
      (X.val 0 0 * X.val 0 0 + X.val 0 1 * X.val 1 0) -
      (Y.val 0 0 * Y.val 0 0 + Y.val 0 1 * Y.val 1 0) = _
  ring

theorem traceZeroForm_nondegenerate (h2 : (2 : K) ≠ 0) :
    (traceZeroForm K).polarBilin.Nondegenerate := by
  have left : (traceZeroForm K).polarBilin.SeparatingLeft := by
    intro X hX
    have h0 := hX (traceZeroCoordinates K ![1, 0, 0])
    have h1 := hX (traceZeroCoordinates K ![0, 0, 1])
    have h2' := hX (traceZeroCoordinates K ![0, 1, 0])
    rw [traceZeroForm_polar] at h0 h1 h2'
    have hx0 : X.val 0 0 = 0 := by
      apply (mul_eq_zero.mp (show (2 : K) * X.val 0 0 = 0 by simpa [traceZeroCoordinates] using h0)).resolve_left h2
    have hx1 : X.val 0 1 = 0 := by simpa [traceZeroCoordinates] using h1
    have hx2 : X.val 1 0 = 0 := by simpa [traceZeroCoordinates] using h2'
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact hx0
    · exact hx1
    · exact hx2
    · change X.val 1 1 = 0
      rw [traceZero_diagonal, hx0, neg_zero]
  refine ⟨left, ?_⟩
  intro X hX
  apply left X
  intro Y
  have h := hX Y
  rw [traceZeroForm_polar] at h ⊢
  linear_combination h

theorem traceZero_square (X : traceZeroSubmodule K) :
    X.val * X.val = traceZeroForm K X • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, traceZeroForm_apply, traceZero_diagonal] <;>
      ring

theorem traceZero_anticommutator (X Y : traceZeroSubmodule K) :
    X.val * Y.val + Y.val * X.val =
      (traceZeroForm K).polarBilin X Y • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [traceZeroForm_polar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, traceZero_diagonal] <;>
      ring

end CFSG.ComponentClassification.CatalogueBOrthogonal
