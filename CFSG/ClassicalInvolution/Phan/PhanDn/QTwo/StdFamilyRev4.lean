module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
import CFSG.ClassicalInvolution.Phan.Phan3TAutA

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary Matrix

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] def swapMat4 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]

omit [Finite K] [CharP K 2] in
theorem swapMat4_mul_self : swapMat4 K * swapMat4 K = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [swapMat4, Matrix.mul_apply, Fin.sum_univ_four]

omit [Finite K] in
theorem det_swapMat4 : (swapMat4 K).det = 1 := by
  rw [Matrix.det_succ_row_zero]
  simp [swapMat4, Fin.sum_univ_succ, Matrix.det_fin_three, CharTwo.neg_eq, Fin.succAbove]

theorem conjTr_swapMat4 :
    conjTr (unitaryInvolution K 2 1) (swapMat4 K) = swapMat4 K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [conjTr, swapMat4]

@[expose] noncomputable def swapSU4 : Su K 2 1 4 :=
  ⟨⟨swapMat4 K, swapMat4 K, swapMat4_mul_self K, swapMat4_mul_self K⟩, by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mk, det_swapMat4]
    · rw [Units.val_mk, conjTr_swapMat4, swapMat4_mul_self]⟩

private theorem rev4_swapSU4_inv : (swapSU4 K)⁻¹ = swapSU4 K :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (Units.ext (swapMat4_mul_self K)))

omit [Finite K] in
private theorem rev4_conj_blockMat_zero (M : Matrix (Fin 3) (Fin 3) K) :
    swapMat4 K * blockMat 4 0 M * swapMat4 K =
      blockMat 4 1 ((swapMat : Matrix (Fin 3) (Fin 3) K) * M * swapMat) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [swapMat4, blockMat, blockSel, swapMat, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four, Fin.sum_univ_three,
      Matrix.sub_apply, Matrix.one_apply, CharTwo.neg_eq]

omit [Finite K] in
private theorem rev4_conj_blockMat_one (M : Matrix (Fin 3) (Fin 3) K) :
    swapMat4 K * blockMat 4 1 M * swapMat4 K =
      blockMat 4 0 ((swapMat : Matrix (Fin 3) (Fin 3) K) * M * swapMat) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [swapMat4, blockMat, blockSel, swapMat, Matrix.mul_apply,
      Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four, Fin.sum_univ_three,
      Matrix.sub_apply, Matrix.one_apply, CharTwo.neg_eq]

omit [Finite K] [CharP K 2] in
private theorem rev4_blockMat_mul_swapMat (i : ℕ) (h : i + 3 ≤ 4)
    (M : Matrix (Fin 3) (Fin 3) K) :
    blockMat 4 i ((swapMat : Matrix (Fin 3) (Fin 3) K) * M * swapMat) =
      blockMat 4 i (swapMat : Matrix (Fin 3) (Fin 3) K) * blockMat 4 i M *
        blockMat 4 i (swapMat : Matrix (Fin 3) (Fin 3) K) := by
  rw [← blockMat_mul h, ← blockMat_mul h]

private theorem rev4_swapElt_mul_self : swapElt K 2 1 * swapElt K 2 1 = 1 := by
  have h := mul_inv_cancel (swapElt K 2 1)
  rwa [swapElt_inv K 2 1] at h

private theorem rev4_blk012_swapElt_inv :
    (blk012 K (swapElt K 2 1))⁻¹ = blk012 K (swapElt K 2 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul, rev4_swapElt_mul_self, map_one]

private theorem rev4_blk123_swapElt_inv :
    (blk123 K (swapElt K 2 1))⁻¹ = blk123 K (swapElt K 2 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul, rev4_swapElt_mul_self, map_one]

private theorem rev4_conj_blk012 (B : Su K 2 1 3) :
    swapSU4 K * blk012 K B * swapSU4 K =
      blk123 K (swapElt K 2 1 * B * (swapElt K 2 1)⁻¹) := by
  rw [map_mul, map_mul, map_inv, rev4_blk123_swapElt_inv]
  refine Subtype.ext (Units.ext ?_)
  change swapMat4 K * blockMat 4 0 ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      swapMat4 K =
    blockMat 4 1 (swapMat : Matrix (Fin 3) (Fin 3) K) *
      blockMat 4 1 ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      blockMat 4 1 (swapMat : Matrix (Fin 3) (Fin 3) K)
  rw [rev4_conj_blockMat_zero]
  rw [rev4_blockMat_mul_swapMat K 1 (by norm_num)]

private theorem rev4_conj_blk123 (B : Su K 2 1 3) :
    swapSU4 K * blk123 K B * swapSU4 K =
      blk012 K (swapElt K 2 1 * B * (swapElt K 2 1)⁻¹) := by
  rw [map_mul, map_mul, map_inv, rev4_blk012_swapElt_inv]
  refine Subtype.ext (Units.ext ?_)
  change swapMat4 K * blockMat 4 1 ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      swapMat4 K =
    blockMat 4 0 (swapMat : Matrix (Fin 3) (Fin 3) K) *
      blockMat 4 0 ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      blockMat 4 0 (swapMat : Matrix (Fin 3) (Fin 3) K)
  rw [rev4_conj_blockMat_one]
  rw [rev4_blockMat_mul_swapMat K 0 (by norm_num)]

@[expose] noncomputable def revSU4 : Su K 2 1 4 ≃* Su K 2 1 4 :=
  (fieldAutSU 2 1 (unitaryInvolution K 2 1) 4).trans (MulAut.conj (swapSU4 K))

theorem revSU4_comp_blk012 :
    (revSU4 K).toMonoidHom.comp (blk012 K) = (blk123 K).comp (revSU3 K 2 1).toMonoidHom := by
  refine MonoidHom.ext fun A => ?_
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, revSU4, MulEquiv.trans_apply,
    MulAut.conj_apply, revSU3, blk012, blk123]
  rw [rev4_swapSU4_inv]
  rw [CFSG.ClassicalInvolution.Phan.Q3G.fieldAutSU_blockEmb]
  exact rev4_conj_blk012 K _

theorem revSU4_comp_blk123 :
    (revSU4 K).toMonoidHom.comp (blk123 K) = (blk012 K).comp (revSU3 K 2 1).toMonoidHom := by
  refine MonoidHom.ext fun A => ?_
  simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, revSU4, MulEquiv.trans_apply,
    MulAut.conj_apply, revSU3, blk012, blk123]
  rw [rev4_swapSU4_inv]
  rw [CFSG.ClassicalInvolution.Phan.Q3G.fieldAutSU_blockEmb]
  exact rev4_conj_blk123 K _

end CFSG.ClassicalInvolution.PhanDn.QTwo
