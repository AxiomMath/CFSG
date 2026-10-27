module

import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

section Parabolic

variable {F : Type*} [CommRing F]

theorem mul_apply_last_castSucc {M N : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ j : Fin 3, M (Fin.last 3) j.castSucc = 0)
    (hN : ∀ j : Fin 3, N (Fin.last 3) j.castSucc = 0) (j : Fin 3) :
    (M * N) (Fin.last 3) j.castSucc = 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [hM, hN, zero_mul, mul_zero, Finset.sum_const_zero, zero_add]

theorem mul_apply_last_last {M N : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ j : Fin 3, M (Fin.last 3) j.castSucc = 0) :
    (M * N) (Fin.last 3) (Fin.last 3) = M (Fin.last 3) (Fin.last 3) * N (Fin.last 3) (Fin.last 3) := by
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [hM, zero_mul, Finset.sum_const_zero, zero_add]

theorem submatrix_castSucc_mul_of_lastRow {M N : Matrix (Fin 4) (Fin 4) F}
    (hN : ∀ j : Fin 3, N (Fin.last 3) j.castSucc = 0) :
    (M * N).submatrix Fin.castSucc Fin.castSucc =
      M.submatrix Fin.castSucc Fin.castSucc * N.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  rw [submatrix_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hN, mul_zero, add_zero,
    Matrix.mul_apply]
  rfl

theorem lastRow_of_mul_eq_one {M N : Matrix (Fin 4) (Fin 4) F} (hMN : M * N = 1)
    (hM : ∀ j : Fin 3, M (Fin.last 3) j.castSucc = 0) :
    (∀ j : Fin 3, N (Fin.last 3) j.castSucc = 0) ∧
      M (Fin.last 3) (Fin.last 3) * N (Fin.last 3) (Fin.last 3) = 1 := by
  have hc : M (Fin.last 3) (Fin.last 3) * N (Fin.last 3) (Fin.last 3) = 1 := by
    rw [← mul_apply_last_last hM, hMN, one_apply_eq]
  refine ⟨fun j => ?_, hc⟩
  have h1 : (M * N) (Fin.last 3) j.castSucc = M (Fin.last 3) (Fin.last 3) * N (Fin.last 3) j.castSucc := by
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [hM, zero_mul, Finset.sum_const_zero, zero_add]
  rw [hMN, one_apply_ne (Fin.castSucc_lt_last j).ne'] at h1
  calc N (Fin.last 3) j.castSucc =
        (N (Fin.last 3) (Fin.last 3) * M (Fin.last 3) (Fin.last 3)) * N (Fin.last 3) j.castSucc := by
          rw [mul_comm (N _ _), hc, one_mul]
    _ = N (Fin.last 3) (Fin.last 3) * (M (Fin.last 3) (Fin.last 3) * N (Fin.last 3) j.castSucc) := by
          ring
    _ = 0 := by rw [← h1, mul_zero]

theorem vecMul_castSucc_of_lastRow {M : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ j : Fin 3, M (Fin.last 3) j.castSucc = 0) (r : Fin 4 → F) :
    (fun j : Fin 3 => (r ᵥ* M) j.castSucc) =
      (fun i : Fin 3 => r i.castSucc) ᵥ* M.submatrix Fin.castSucc Fin.castSucc := by
  funext j
  simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, hM, mul_zero, add_zero, submatrix_apply]

theorem submatrix_castSucc_one :
    (1 : Matrix (Fin 4) (Fin 4) F).submatrix Fin.castSucc Fin.castSucc = 1 :=
  submatrix_one_embedding ⟨Fin.castSucc, Fin.castSucc_injective 3⟩

end Parabolic

section Radical

variable {F : Type*} [CommRing F]

@[expose] def IsColRadical (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  (∀ (i : Fin 4) (j : Fin 3), M i j.castSucc = (1 : Matrix (Fin 4) (Fin 4) F) i j.castSucc) ∧
    M (Fin.last 3) (Fin.last 3) = 1

@[expose] def colRadVec (M : Matrix (Fin 4) (Fin 4) F) : Fin 3 → F :=
  fun i => M i.castSucc (Fin.last 3)

theorem IsColRadical.lastRow {M : Matrix (Fin 4) (Fin 4) F} (hM : IsColRadical M) (j : Fin 3) :
    M (Fin.last 3) j.castSucc = 0 := by
  rw [hM.1, one_apply_ne (Fin.castSucc_lt_last j).ne']

theorem IsColRadical.mul {M N : Matrix (Fin 4) (Fin 4) F} (hM : IsColRadical M)
    (hN : IsColRadical N) :
    IsColRadical (M * N) ∧ colRadVec (M * N) = colRadVec M + colRadVec N := by
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · rw [Matrix.mul_apply]
    simp only [hN.1, one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [hM.1, one_apply]
  · rw [mul_apply_last_last hM.lastRow, hM.2, hN.2, one_mul]
  · funext i
    have h1 : ∀ x : Fin 3, (i.castSucc = x.castSucc) = (i = x) :=
      fun x => propext Fin.castSucc_inj
    simp only [colRadVec, Pi.add_apply]
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [hM.1, hN.2, mul_one, one_apply, ite_mul, one_mul, zero_mul, h1,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring

theorem IsColRadical.eq_one {M : Matrix (Fin 4) (Fin 4) F} (hM : IsColRadical M)
    (h0 : colRadVec M = 0) : M = 1 := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => rw [hM.2, one_apply_eq]
    | cast i =>
      have h := congrFun h0 i
      simp only [colRadVec, Pi.zero_apply] at h
      rw [h, one_apply_ne (Fin.castSucc_lt_last i).ne]
  | cast j => exact hM.1 i j

theorem colRadVec_eq_mulVec_of_mul_eq {x M M' : Matrix (Fin 4) (Fin 4) F}
    (hx1 : x (Fin.last 3) (Fin.last 3) = 1)
    (hM : IsColRadical M) (hM' : IsColRadical M') (h : x * M = M' * x) :
    colRadVec M' = x.submatrix Fin.castSucc Fin.castSucc *ᵥ colRadVec M := by
  funext i
  have h2 : ∀ x' : Fin 3, (i.castSucc = x'.castSucc) = (i = x') :=
    fun x' => propext Fin.castSucc_inj
  have hL : (x * M) i.castSucc (Fin.last 3) =
      (x.submatrix Fin.castSucc Fin.castSucc *ᵥ colRadVec M) i + x i.castSucc (Fin.last 3) := by
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, hM.2, mul_one]
    rfl
  have hR : (M' * x) i.castSucc (Fin.last 3) = x i.castSucc (Fin.last 3) + colRadVec M' i := by
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, hx1, mul_one]
    simp only [hM'.1, one_apply, ite_mul, one_mul, zero_mul, h2, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rfl
  have h1 := congrFun (congrFun h i.castSucc) (Fin.last 3)
  rw [hL, hR] at h1
  linear_combination -h1

theorem IsColRadical.ext {M M' : Matrix (Fin 4) (Fin 4) F} (hM : IsColRadical M)
    (hM' : IsColRadical M') (h : colRadVec M = colRadVec M') : M = M' := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => rw [hM.2, hM'.2]
    | cast i => exact congrFun h i
  | cast j => rw [hM.1, hM'.1]

theorem det_eq_of_lastRow {M : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ j : Fin 3, M (Fin.last 3) j.castSucc = 0) :
    M.det = M (Fin.last 3) (Fin.last 3) * (M.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row M (Fin.last 3), Fin.sum_univ_castSucc]
  simp only [hM, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last,
    Fin.val_last]
  norm_num

@[expose] def colRadMat (s : Fin 3 → F) : Matrix (Fin 4) (Fin 4) F :=
  1 + Matrix.of fun p q => if q = Fin.last 3 then Fin.lastCases 0 s p else 0

theorem isColRadical_colRadMat (s : Fin 3 → F) : IsColRadical (colRadMat s) := by
  refine ⟨fun i j => ?_, ?_⟩
  · rw [colRadMat, Matrix.add_apply, of_apply, ite_eq_right_iff.2 fun h =>
      absurd h (Fin.castSucc_lt_last j).ne, add_zero]
  · rw [colRadMat, Matrix.add_apply, of_apply, ite_eq_left_iff.2 fun h => absurd rfl h,
      Fin.lastCases_last, add_zero, one_apply_eq]

theorem colRadVec_colRadMat (s : Fin 3 → F) : colRadVec (colRadMat s) = s := by
  funext i
  rw [colRadVec, colRadMat, Matrix.add_apply, of_apply, ite_eq_left_iff.2 fun h => absurd rfl h,
    Fin.lastCases_castSucc, one_apply_ne (Fin.castSucc_lt_last i).ne, zero_add]

theorem det_colRadMat (s : Fin 3 → F) : (colRadMat s).det = 1 := by
  rw [det_eq_of_lastRow (isColRadical_colRadMat s).lastRow, (isColRadical_colRadMat s).2, one_mul]
  have h : (colRadMat s).submatrix Fin.castSucc Fin.castSucc = 1 := by
    ext i j
    rw [submatrix_apply, (isColRadical_colRadMat s).1, one_apply, one_apply]
    simp only [Fin.castSucc_inj]
  rw [h, det_one]

end Radical

end CFSG.SeitzReduction.LinearPilot
