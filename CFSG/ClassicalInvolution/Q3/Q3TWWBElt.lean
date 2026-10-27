module

public import CFSG.ClassicalInvolution.Q3.Q3TWWSU4

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.ClassicalInvolution.Q3.Q3Z CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.WeakCT.SU4
open scoped Matrix

@[expose] def nB9 : Matrix (Fin 4) (Fin 4) F9 :=
  !![0, 0, 0, iota9; 0, 0, iota9, 0; 0, iota9, 0, 0; iota9, 0, 0, 0]

theorem su4_B_F9 :
    nF9 0 * (nF9 1 * nF9 1) * nF9 0 * nF9 2 * (nF9 3 * nF9 3) * nF9 2 = nB9 := by
  decide +kernel

theorem su4_B_conj2 : nF9 2 * nB9 = nB9 * (nF9 3 * nF9 3) := by decide +kernel

theorem su4_B_conj3 : nF9 3 * nB9 = nB9 * (nF9 2 * nF9 2) := by decide +kernel

section KPart

variable {K : Type} [Field K] [CharP K 3]

@[expose] def bMat (ι : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, ι; 0, 0, ι, 0; 0, ι, 0, 0; ι, 0, 0, 0]

variable (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 3) (hσσ : ∀ c, σ (σ c) = c) (ι : K)
  (hι : ι ^ 2 = -1)

@[expose] noncomputable def suB : SU σ 4 :=
  suLetter σ hσ hσσ ι hι 0 * (suLetter σ hσ hσσ ι hι 1 * suLetter σ hσ hσσ ι hι 1) *
    suLetter σ hσ hσσ ι hι 0 * suLetter σ hσ hσσ ι hι 2 *
    (suLetter σ hσ hσσ ι hι 3 * suLetter σ hσ hσσ ι hι 3) * suLetter σ hσ hσσ ι hι 2

theorem map_nB9 : (phi9 ι hι).mapMatrix nB9 = bMat ι := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nB9, bMat, phi9_iota9 ι hι]

theorem suMat_suB : suMat σ (suB σ hσ hσσ ι hι) = bMat ι := by
  have h := congrArg (phi9 ι hι).mapMatrix su4_B_F9
  simp only [map_mul, map_nB9 ι hι] at h
  simpa only [suB, map_mul, suMat_suLetter σ hσ hσσ ι hι] using h

theorem suLetter_cube (j : Fin 12) :
    suLetter σ hσ hσσ ι hι j * suLetter σ hσ hσσ ι hι j * suLetter σ hσ hσσ ι hι j = 1 := by
  apply suMat_injective σ
  have h := congrArg (phi9 ι hι).mapMatrix (su4_cube_F9 j)
  simp only [map_mul, map_one] at h
  simpa only [map_mul, map_one, suMat_suLetter σ hσ hσσ ι hι] using h

theorem suLetter_conj2 : suLetter σ hσ hσσ ι hι 2 * suB σ hσ hσσ ι hι =
    suB σ hσ hσσ ι hι * (suLetter σ hσ hσσ ι hι 3 * suLetter σ hσ hσσ ι hι 3) := by
  apply suMat_injective σ
  have h := congrArg (phi9 ι hι).mapMatrix su4_B_conj2
  simp only [map_mul, map_nB9 ι hι] at h
  simpa only [map_mul, suMat_suLetter σ hσ hσσ ι hι, suMat_suB σ hσ hσσ ι hι] using h

theorem suLetter_conj3 : suLetter σ hσ hσσ ι hι 3 * suB σ hσ hσσ ι hι =
    suB σ hσ hσσ ι hι * (suLetter σ hσ hσσ ι hι 2 * suLetter σ hσ hσσ ι hι 2) := by
  apply suMat_injective σ
  have h := congrArg (phi9 ι hι).mapMatrix su4_B_conj3
  simp only [map_mul, map_nB9 ι hι] at h
  simpa only [map_mul, suMat_suLetter σ hσ hσσ ι hι, suMat_suB σ hσ hσσ ι hι] using h

omit [CharP K 3] in
theorem bMat_mul_rootMatrix_01 (σ' : K ≃+* K) (h' : ∀ c, σ' (σ' c) = c) (ι' c : K) :
    bMat ι' * rootMatrix σ' 0 1 c = rootMatrix σ' 1 0 (-σ' c) * bMat ι' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bMat, rootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
      Fin.rev, h'] <;> ring

omit [CharP K 3] in
theorem bMat_mul_rootMatrix_10 (σ' : K ≃+* K) (h' : ∀ c, σ' (σ' c) = c) (ι' c : K) :
    bMat ι' * rootMatrix σ' 1 0 c = rootMatrix σ' 0 1 (-σ' c) * bMat ι' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bMat, rootMatrix, Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
      Fin.rev, h'] <;> ring

theorem suB_mul_suroot01 (c : K) :
    suB σ hσ hσσ ι hι * suroot σ hσσ 0 1 (by decide) (by decide) (by decide) c =
      suroot σ hσσ 1 0 (by decide) (by decide) (by decide) (-σ c) * suB σ hσ hσσ ι hι := by
  apply suMat_injective σ
  rw [map_mul, map_mul, suMat_suB σ hσ hσσ ι hι]
  exact bMat_mul_rootMatrix_01 σ hσσ ι c

theorem suB_mul_suroot10 (c : K) :
    suB σ hσ hσσ ι hι * suroot σ hσσ 1 0 (by decide) (by decide) (by decide) c =
      suroot σ hσσ 0 1 (by decide) (by decide) (by decide) (-σ c) * suB σ hσ hσσ ι hι := by
  apply suMat_injective σ
  rw [map_mul, map_mul, suMat_suB σ hσ hσσ ι hι]
  exact bMat_mul_rootMatrix_10 σ hσσ ι c

theorem suB_conj01 (c : K) :
    suB σ hσ hσσ ι hι * suroot σ hσσ 0 1 (by decide) (by decide) (by decide) c *
        (suB σ hσ hσσ ι hι)⁻¹ =
      suroot σ hσσ 1 0 (by decide) (by decide) (by decide) (-σ c) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact suB_mul_suroot01 σ hσ hσσ ι hι c

theorem suB_conj10 (c : K) :
    suB σ hσ hσσ ι hι * suroot σ hσσ 1 0 (by decide) (by decide) (by decide) c *
        (suB σ hσ hσσ ι hι)⁻¹ =
      suroot σ hσσ 0 1 (by decide) (by decide) (by decide) (-σ c) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact suB_mul_suroot10 σ hσ hσσ ι hι c

theorem suB_inv_conj01 (c : K) :
    (suB σ hσ hσσ ι hι)⁻¹ * suroot σ hσσ 0 1 (by decide) (by decide) (by decide) c *
        suB σ hσ hσσ ι hι =
      suroot σ hσσ 1 0 (by decide) (by decide) (by decide) (-σ c) := by
  have h := suB_mul_suroot10 σ hσ hσσ ι hι (-σ c)
  rw [map_neg, hσσ, neg_neg] at h
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  exact h.symm

theorem suB_inv_conj10 (c : K) :
    (suB σ hσ hσσ ι hι)⁻¹ * suroot σ hσσ 1 0 (by decide) (by decide) (by decide) c *
        suB σ hσ hσσ ι hι =
      suroot σ hσσ 0 1 (by decide) (by decide) (by decide) (-σ c) := by
  have h := suB_mul_suroot01 σ hσ hσσ ι hι (-σ c)
  rw [map_neg, hσσ, neg_neg] at h
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  exact h.symm

end KPart

end CFSG.ClassicalInvolution.Q3.Q3TW
