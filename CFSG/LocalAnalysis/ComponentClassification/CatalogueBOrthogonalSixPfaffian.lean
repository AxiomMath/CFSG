module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap

variable {F : Type*} [CommRing F]

@[expose] def skewMatrix (a b c d e f : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, a, b, c; -a, 0, d, e; -b, -d, 0, f; -c, -e, -f, 0]

theorem skewMatrix_transpose (a b c d e f : F) :
    (skewMatrix a b c d e f).transpose = -skewMatrix a b c d e f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skewMatrix]

@[expose] def pfaffian (X : Matrix (Fin 4) (Fin 4) F) : F :=
  X 0 1 * X 2 3 - X 0 2 * X 1 3 + X 0 3 * X 1 2

theorem pfaffian_skewMatrix (a b c d e f : F) :
    pfaffian (skewMatrix a b c d e f) = a * f - b * e + c * d := rfl

@[expose] def sharp (X : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 4) (Fin 4) F :=
  skewMatrix (X 2 3) (-X 1 3) (X 1 2) (X 0 3) (-X 0 2) (X 0 1)

theorem sharp_skewMatrix (a b c d e f : F) :
    sharp (skewMatrix a b c d e f) = skewMatrix f (-e) d c (-b) a := rfl

theorem sharp_add (X Y : Matrix (Fin 4) (Fin 4) F) :
    sharp (X + Y) = sharp X + sharp Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sharp, skewMatrix] <;> ring

theorem sharp_smul (a : F) (X : Matrix (Fin 4) (Fin 4) F) :
    sharp (a • X) = a • sharp X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sharp, skewMatrix, smul_eq_mul]

theorem sharp_sharp_skewMatrix (a b c d e f : F) :
    sharp (sharp (skewMatrix a b c d e f)) = skewMatrix a b c d e f := by
  simp only [sharp_skewMatrix, neg_neg]

theorem pfaffian_sharp_skewMatrix (a b c d e f : F) :
    pfaffian (sharp (skewMatrix a b c d e f)) =
      pfaffian (skewMatrix a b c d e f) := by
  simp only [sharp_skewMatrix, pfaffian_skewMatrix]
  ring

theorem skewMatrix_mul_sharp (a b c d e f : F) :
    skewMatrix a b c d e f * sharp (skewMatrix a b c d e f) =
      -(pfaffian (skewMatrix a b c d e f)) • (1 : Matrix (Fin 4) (Fin 4) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, sharp, skewMatrix, pfaffian, smul_eq_mul] <;>
    ring

theorem sharp_mul_skewMatrix (a b c d e f : F) :
    sharp (skewMatrix a b c d e f) * skewMatrix a b c d e f =
      -(pfaffian (skewMatrix a b c d e f)) • (1 : Matrix (Fin 4) (Fin 4) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, sharp, skewMatrix, pfaffian, smul_eq_mul] <;>
    ring

theorem skewMatrix_det (a b c d e f : F) :
    (skewMatrix a b c d e f).det = pfaffian (skewMatrix a b c d e f) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, skewMatrix, pfaffian,
    Fin.succAbove]
  ring

@[expose] def pfaffianForm (F : Type*) [CommRing F] :
    QuadraticForm F (Matrix (Fin 4) (Fin 4) F) :=
  linMulLin (Matrix.entryLinearMap F F 0 1) (Matrix.entryLinearMap F F 2 3) -
    linMulLin (Matrix.entryLinearMap F F 0 2) (Matrix.entryLinearMap F F 1 3) +
    linMulLin (Matrix.entryLinearMap F F 0 3) (Matrix.entryLinearMap F F 1 2)

theorem pfaffianForm_apply (X : Matrix (Fin 4) (Fin 4) F) :
    pfaffianForm F X = pfaffian X := rfl

theorem pfaffian_smul (a : F) (X : Matrix (Fin 4) (Fin 4) F) :
    pfaffian (a • X) = a ^ 2 * pfaffian X := by
  change pfaffianForm F (a • X) = a ^ 2 * pfaffianForm F X
  rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]

theorem skewMatrix_polarized_product (a b c d e f a' b' c' d' e' f' : F) :
    skewMatrix a b c d e f * sharp (skewMatrix a' b' c' d' e' f') +
      skewMatrix a' b' c' d' e' f' * sharp (skewMatrix a b c d e f) =
      -(pfaffian (skewMatrix a b c d e f + skewMatrix a' b' c' d' e' f') -
        pfaffian (skewMatrix a b c d e f) -
          pfaffian (skewMatrix a' b' c' d' e' f')) • (1 : Matrix (Fin 4) (Fin 4) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sharp, skewMatrix, pfaffian, smul_eq_mul] <;>
    ring

@[expose] def skewSubmodule (F : Type*) [CommRing F] :
    Submodule F (Matrix (Fin 4) (Fin 4) F) where
  carrier := {X | X.transpose = -X}
  zero_mem' := by simp
  add_mem' {X} {Y} hX hY := by
    change (X + Y).transpose = -(X + Y)
    rw [Matrix.transpose_add, hX, hY, neg_add]
  smul_mem' a X hX := by
    change (a • X).transpose = -(a • X)
    rw [Matrix.transpose_smul, hX, smul_neg]

theorem mem_skewSubmodule (X : Matrix (Fin 4) (Fin 4) F) :
    X ∈ skewSubmodule F ↔ X.transpose = -X := Iff.rfl

theorem sharp_transpose (X : Matrix (Fin 4) (Fin 4) F) :
    (sharp X).transpose = -sharp X := skewMatrix_transpose _ _ _ _ _ _

section Field

variable {K : Type*} [Field K]

theorem skew_diagonal_zero (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 4) (Fin 4) K} (hX : X.transpose = -X) (i : Fin 4) :
    X i i = 0 := by
  have h : X i i = -X i i := congrArg (fun M => M i i) hX
  have hmul : (2 : K) * X i i = 0 := by
    calc
      (2 : K) * X i i = X i i + X i i := by ring
      _ = -X i i + X i i := congrArg (fun x => x + X i i) h
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp hmul).resolve_left h2

theorem skew_eq_skewMatrix (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 4) (Fin 4) K} (hX : X.transpose = -X) :
    X = skewMatrix (X 0 1) (X 0 2) (X 0 3) (X 1 2) (X 1 3) (X 2 3) := by
  have hl : ∀ i j, X j i = -X i j := fun i j => congrArg (fun M => M i j) hX
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact skew_diagonal_zero h2 hX _
    | rfl
    | exact hl _ _

theorem sharp_sharp (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 4) (Fin 4) K} (hX : X.transpose = -X) :
    sharp (sharp X) = X := by
  rw [skew_eq_skewMatrix h2 hX]
  exact sharp_sharp_skewMatrix _ _ _ _ _ _

theorem pfaffian_sharp (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 4) (Fin 4) K} (hX : X.transpose = -X) :
    pfaffian (sharp X) = pfaffian X := by
  rw [skew_eq_skewMatrix h2 hX]
  exact pfaffian_sharp_skewMatrix _ _ _ _ _ _

theorem mul_sharp (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 4) (Fin 4) K} (hX : X.transpose = -X) :
    X * sharp X = -pfaffian X • (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [skew_eq_skewMatrix h2 hX]
  exact skewMatrix_mul_sharp _ _ _ _ _ _

theorem sharp_mul (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 4) (Fin 4) K} (hX : X.transpose = -X) :
    sharp X * X = -pfaffian X • (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [skew_eq_skewMatrix h2 hX]
  exact sharp_mul_skewMatrix _ _ _ _ _ _

theorem skew_det (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 4) (Fin 4) K} (hX : X.transpose = -X) :
    X.det = pfaffian X ^ 2 := by
  rw [skew_eq_skewMatrix h2 hX]
  exact skewMatrix_det _ _ _ _ _ _

theorem polarized_product (h2 : (2 : K) ≠ 0)
    {X Y : Matrix (Fin 4) (Fin 4) K} (hX : X.transpose = -X) (hY : Y.transpose = -Y) :
    X * sharp Y + Y * sharp X =
      -(pfaffian (X + Y) - pfaffian X - pfaffian Y) •
        (1 : Matrix (Fin 4) (Fin 4) K) := by
  rw [skew_eq_skewMatrix h2 hX, skew_eq_skewMatrix h2 hY]
  exact skewMatrix_polarized_product _ _ _ _ _ _ _ _ _ _ _ _

end Field

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
