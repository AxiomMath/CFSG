module

public import CFSG.ClassicalInvolution.WeakCT.Center

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix
open CFSG.ClassicalInvolution.Phan (swapMat swapMat_mul_self det_swapMat rotMat rotMatInv
  rotMat_mul_rotMatInv rotMatInv_mul_rotMat det_rotMat swapMat_mul_embPair_two
  swapMat_mul_embPair_zero embPair_two_eq_blockMat embPair_zero_eq_blockMat)
open scoped MatrixGroups

section Automorphism

variable {G X : Type*} [Group G] [Group X]

theorem range_comp_mulEquiv (θ : G →* X) (e : G ≃* G) :
    (θ.comp e.toMonoidHom).range = θ.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, by simp⟩

theorem ker_comp_mulEquiv_le_center {θ : G →* X} (hθ : θ.ker ≤ Subgroup.center G) (e : G ≃* G) :
    (θ.comp e.toMonoidHom).ker ≤ Subgroup.center G := fun _ hx =>
  (MulEquivClass.apply_mem_center_iff e).1 (hθ hx)

theorem map_comp_mulEquiv (θ : G →* X) (e : G ≃* G) (H : Subgroup G) :
    H.map (θ.comp e.toMonoidHom) = (H.map e.toMonoidHom).map θ :=
  (Subgroup.map_map _ _ _).symm

end Automorphism

section Swap

variable {K : Type} [Field K]

@[expose] def swapSL : SL(3, K) :=
  ⟨swapMat, det_swapMat⟩

@[expose] def rotSL : SL(2, K) :=
  ⟨rotMat, det_rotMat⟩

theorem swapSL_inv : (swapSL : SL(3, K))⁻¹ = swapSL :=
  inv_eq_of_mul_eq_one_right (Subtype.ext swapMat_mul_self)

theorem coe_rotSL_inv : (((rotSL : SL(2, K))⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
    rotMatInv := by
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotSL, rotMat, rotMatInv, Matrix.adjugate_fin_two]

theorem coe_swapSL : ((swapSL : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = swapMat :=
  rfl

theorem swapSL_mul_blockSL_zero_mul_inv (A : SL(2, K)) :
    swapSL * blockSL K 3 2 0 (by omega) A * swapSL⁻¹ =
      blockSL K 3 2 1 (by omega) (rotSL * A * rotSL⁻¹) := by
  rw [swapSL_inv]
  have h := swapMat_mul_embPair_two (A : Matrix (Fin 2) (Fin 2) K)
  rw [embPair_two_eq_blockMat, embPair_zero_eq_blockMat] at h
  have h' : (((swapSL : SL(3, K)) * blockSL K 3 2 0 (by omega) A * swapSL : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) =
      ((blockSL K 3 2 1 (by omega) (rotSL * A * rotSL⁻¹) : SL(3, K)) :
        Matrix (Fin 3) (Fin 3) K) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_rotSL_inv, coe_swapSL]
    exact h
  exact Subtype.ext h'

theorem swapSL_mul_blockSL_one_mul_inv (A : SL(2, K)) :
    swapSL * blockSL K 3 2 1 (by omega) A * swapSL⁻¹ =
      blockSL K 3 2 0 (by omega) (rotSL * A * rotSL⁻¹) := by
  rw [swapSL_inv]
  have h := swapMat_mul_embPair_zero (A : Matrix (Fin 2) (Fin 2) K)
  rw [embPair_two_eq_blockMat, embPair_zero_eq_blockMat] at h
  have h' : (((swapSL : SL(3, K)) * blockSL K 3 2 1 (by omega) A * swapSL : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) =
      ((blockSL K 3 2 0 (by omega) (rotSL * A * rotSL⁻¹) : SL(3, K)) :
        Matrix (Fin 3) (Fin 3) K) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_rotSL_inv, coe_swapSL]
    exact h
  exact Subtype.ext h'

theorem map_conj_swapSL_B12 :
    (B12 K).map (MulAut.conj (swapSL : SL(3, K))).toMonoidHom = B23 K := by
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨_, (swapSL_mul_blockSL_zero_mul_inv A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨blockSL K 3 2 0 (by omega) ((rotSL)⁻¹ * A * rotSL), ⟨_, rfl⟩, ?_⟩
    change swapSL * _ * swapSL⁻¹ = _
    rw [swapSL_mul_blockSL_zero_mul_inv]
    congr 1
    group

theorem map_conj_swapSL_B23 :
    (B23 K).map (MulAut.conj (swapSL : SL(3, K))).toMonoidHom = B12 K := by
  ext x
  constructor
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨_, (swapSL_mul_blockSL_one_mul_inv A).symm⟩
  · rintro ⟨A, rfl⟩
    refine ⟨blockSL K 3 2 1 (by omega) ((rotSL)⁻¹ * A * rotSL), ⟨_, rfl⟩, ?_⟩
    change swapSL * _ * swapSL⁻¹ = _
    rw [swapSL_mul_blockSL_one_mul_inv]
    congr 1
    group

end Swap

section Normalize

variable {K : Type} [Field K] {X : Type} [Group X]

theorem pair_normalize {W U V : Subgroup X} (h : LinearBlockStandardPair K W U V) :
    ∃ θ : SL(3, K) →* X, θ.range = W ∧ θ.ker ≤ Subgroup.center SL(3, K) ∧
      (B12 K).map θ = U ∧ (B23 K).map θ = V := by
  obtain ⟨θ, c, hrange, hker, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h
  · refine ⟨θ.comp (MulAut.conj c⁻¹).toMonoidHom, ?_, ker_comp_mulEquiv_le_center hker _, ?_, ?_⟩
    · rw [range_comp_mulEquiv, hrange]
    · rw [map_comp_mulEquiv, h1]
    · rw [map_comp_mulEquiv, h2]
  · have e : (MulAut.conj (c⁻¹ * (swapSL : SL(3, K)))).toMonoidHom =
        (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj (swapSL : SL(3, K))).toMonoidHom := by
      ext x
      simp [mul_assoc]
    refine ⟨θ.comp (MulAut.conj (c⁻¹ * (swapSL : SL(3, K)))).toMonoidHom, ?_,
      ker_comp_mulEquiv_le_center hker _, ?_, ?_⟩
    · rw [range_comp_mulEquiv, hrange]
    · rw [map_comp_mulEquiv, e, ← Subgroup.map_map, map_conj_swapSL_B12, h2]
    · rw [map_comp_mulEquiv, e, ← Subgroup.map_map, map_conj_swapSL_B23, h1]

theorem pair_block_inj {θ : SL(3, K) →* X} (hker : θ.ker ≤ Subgroup.center SL(3, K))
    {U V : Subgroup X} (hU : (B12 K).map θ = U) (hV : (B23 K).map θ = V) :
    Function.Injective (θ.comp (blockSL K 3 2 0 (by omega))) ∧
      (θ.comp (blockSL K 3 2 0 (by omega))).range = U ∧
      Function.Injective (θ.comp (blockSL K 3 2 1 (by omega))) ∧
      (θ.comp (blockSL K 3 2 1 (by omega))).range = V :=
  ⟨comp_blockSL_injective hker _ (by omega), by rw [MonoidHom.range_comp, ← hU]; rfl,
    comp_blockSL_injective hker _ (by omega), by rw [MonoidHom.range_comp, ← hV]; rfl⟩

end Normalize

end CFSG.ClassicalInvolution.WeakCT
