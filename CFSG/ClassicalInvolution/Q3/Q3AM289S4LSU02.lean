module

public import CFSG.ClassicalInvolution.Q3.Q3MFOU4F9

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Q3.Q3PP (F9 two_ne_zero_F9)

section Pairs

@[expose] def pair01 : Pair 4 := ⟨{0, 1}, by decide⟩

@[expose] def pair02 : Pair 4 := ⟨{0, 2}, by decide⟩

@[expose] def pair12 : Pair 4 := ⟨{1, 2}, by decide⟩

theorem zMat_pair01 : zMat F9 4 pair01.1 = Matrix.diagonal ![-1, -1, 1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pair01, zMat]

theorem zMat_pair02 : zMat F9 4 pair02.1 = Matrix.diagonal ![-1, 1, -1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pair02, zMat]

theorem zMat_pair12 : zMat F9 4 pair12.1 = Matrix.diagonal ![1, -1, -1, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [pair12, zMat]

theorem zEltU_pair01_mul_pair02 :
    zEltU F9 3 1 pair01 * zEltU F9 3 1 pair02 = zEltU F9 3 1 pair12 := by
  apply suMat_injective
  rw [suMat_mul, suMat_zEltU, suMat_zEltU, suMat_zEltU, zMat_pair01, zMat_pair02, zMat_pair12,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> simp

theorem zEltU_pair02_mul_pair01 :
    zEltU F9 3 1 pair02 * zEltU F9 3 1 pair01 = zEltU F9 3 1 pair12 := by
  rw [← zEltU_pair01_mul_pair02]
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_zEltU, suMat_zEltU, zMat_pair01, zMat_pair02,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> simp

end Pairs

section Elements

variable {i : F9}

theorem conjTr_diagonal_F9 (σ : F9 ≃+* F9) {n : ℕ} (d : Fin n → F9) :
    conjTr σ (Matrix.diagonal d) = Matrix.diagonal fun a => σ (d a) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp [conjTr]
  · simp [conjTr, h, Ne.symm h]

@[expose] noncomputable def uElt (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    Su F9 3 1 4 :=
  have hσi' : (frobenius F9 3) i = -i := by simpa using hσi
  Models.mkSU F9 3 1 (Matrix.diagonal ![i, 1, -i, 1]) (by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp
    linear_combination -hi) (by
    rw [conjTr_diagonal_F9, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    fin_cases a <;> simp [hσi'] <;> linear_combination -hi)

theorem suMat_uElt (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    suMat (uElt hi hσi) = Matrix.diagonal ![i, 1, -i, 1] := rfl

theorem uElt_mul_self (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    uElt hi hσi * uElt hi hσi = zEltU F9 3 1 pair02 := by
  apply suMat_injective
  rw [suMat_mul, suMat_uElt, suMat_zEltU, zMat_pair02, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> simp [hi]

theorem uElt_comm (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    uElt hi hσi * zEltU F9 3 1 pair01 = zEltU F9 3 1 pair01 * uElt hi hσi := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_uElt, suMat_zEltU, zMat_pair01, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  fin_cases a <;> simp [mul_comm]

theorem uElt_mem_LcU (hi : i * i = -1) (hσi : unitaryInvolution F9 3 1 i = -i) :
    uElt hi hσi ∈ LcU F9 3 1 pair02 := by
  show uElt hi hσi ∈ longRootGroupSU F9 3 1 (zMat F9 4 pair02.1)
  rw [mem_longRootGroupSU, suMat_uElt, zMat_pair02]
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply]

end Elements

section Center

@[expose] noncomputable def wElt : Su F9 3 1 2 :=
  Models.mkSU F9 3 1 !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
    (by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two])

theorem suMat_wElt : suMat wElt = !![0, 1; -1, 0] := rfl

theorem suMat_blockEmb_zero_four (A : Su F9 3 1 2) :
    suMat (blockEmb F9 3 1 4 2 0 (by norm_num) A) =
      !![suMat A 0 0, suMat A 0 1, 0, 0; suMat A 1 0, suMat A 1 1, 0, 0; 0, 0, 1, 0;
        0, 0, 0, 1] := by
  rw [suMat_blockEmb]
  ext a b
  rw [Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem suMat_blockEmb_one_four_wElt :
    suMat (blockEmb F9 3 1 4 2 1 (by norm_num) wElt) =
      !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1] := by
  rw [suMat_blockEmb, suMat_wElt]
  ext a b
  rw [Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem zEltU_pair01_eq :
    zEltU F9 3 1 pair01 = blockEmb F9 3 1 4 2 0 (by norm_num) (negOneSU F9 3 1) := by
  apply suMat_injective
  rw [suMat_zEltU, zMat_pair01, suMat_blockEmb, suMat_negOneSU]
  ext a b
  rw [Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem eq_one_of_blockEmb_central {A : Su F9 3 1 2}
    (h : blockEmb F9 3 1 4 2 0 (by norm_num) A ∈ Subgroup.center (Su F9 3 1 4)) : A = 1 := by
  have hc := Subgroup.mem_center_iff.mp h (blockEmb F9 3 1 4 2 1 (by norm_num) wElt)
  have h1 := congrArg suMat hc
  rw [suMat_mul, suMat_mul, suMat_blockEmb_zero_four, suMat_blockEmb_one_four_wElt] at h1
  have e01 := congrFun (congrFun h1 0) 1
  have e10 := congrFun (congrFun h1 1) 0
  have e12 := congrFun (congrFun h1 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e01 e10 e12
  have hdet := det_suMat A
  rw [Matrix.det_fin_two] at hdet
  have hA10 : suMat A 1 0 = 0 := e10.symm
  have hA11 : suMat A 1 1 = 1 := e12.symm
  have hA01 : suMat A 0 1 = 0 := e01
  have hA00 : suMat A 0 0 = 1 := by
    rw [hA10, hA11] at hdet
    linear_combination hdet
  apply suMat_injective
  ext a b
  fin_cases a <;> fin_cases b <;> simp [hA00, hA01, hA10, hA11]

theorem LcU_center (T : Pair 4) {y : Su F9 3 1 4} (hy : y ∈ LcU F9 3 1 T)
    (hc : y ∈ Subgroup.center (Su F9 3 1 4)) : y = 1 := by
  obtain ⟨g, hg⟩ := (mem_longRootSetU_iff (by norm_num)).mp
    (LcU_mem_longRootSetU two_ne_zero_F9 (by norm_num) T)
  rw [hg, mem_map_conj_iff_of_group] at hy
  have hyc : g⁻¹ * y * g = y := by
    rw [Subgroup.mem_center_iff.mp hc g⁻¹]
    exact inv_mul_cancel_right y g
  rw [hyc] at hy
  obtain ⟨A, rfl⟩ := hy
  rw [eq_one_of_blockEmb_central hc, map_one]

end Center

end CFSG.ClassicalInvolution.Q3.Q3AM
