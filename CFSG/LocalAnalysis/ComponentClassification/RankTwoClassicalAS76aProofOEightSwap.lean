module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightMat
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOLayer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOSiegel

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Swap

variable {K : Type} [Field K]

@[expose] def swapOneGL : GL (Fin 2 ⊕ Fin 2) K :=
  ⟨swapOneMat, swapOneMat, swapOneMat_mul_self, swapOneMat_mul_self⟩

theorem swapOneGL_mul_self : (swapOneGL : GL (Fin 2 ⊕ Fin 2) K) * swapOneGL = 1 :=
  Units.ext swapOneMat_mul_self

theorem swapOneMat_sub_one_mulVec [CharP K 2] (u : Fin 2 ⊕ Fin 2 → K) :
    (swapOneMat - 1) *ᵥ u = (u (.inl 1) + u (.inr 1)) • (uE (.inl 1) + uE (.inr 1)) := by
  funext c
  rcases c with s | s <;> fin_cases s <;>
    simp [swapOneMat, mulVec, dotProduct, Fintype.sum_sum_type, single_apply,
      CharTwo.sub_eq_add, CharTwo.add_self_eq_zero]

end Swap

section Rank

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

theorem commRank_oblkGL_swap {s₂ : GL ι₂ K} {b₂ : ι₂ → K} {φ : (ι₂ → K) → K}
    (hs₂ : ∀ w, ((s₂ : Matrix ι₂ ι₂ K) - 1) *ᵥ w = φ w • b₂) (hb₂ : b₂ ≠ 0) {w₁ : ι₂ → K}
    (hw₁ : φ w₁ = 1) : commRank (oblkGL oe (s₂, swapOneGL)) = 2 := by
  have hX : ((oblkGL oe (s₂, swapOneGL) : GL ι K) : Matrix ι ι K) - 1 =
      oblk oe ((s₂ : Matrix ι₂ ι₂ K) - 1) (swapOneMat - 1) := by
    rw [coe_oblkGL, ← oblk_one (oe := oe), sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg,
      ← neg_one_smul K (oblk oe 1 1), oblk_smul, oblk_add, neg_one_smul, neg_one_smul]
    rfl
  have hv : ∀ v, (((oblkGL oe (s₂, swapOneGL) : GL ι K) : Matrix ι ι K) - 1) *ᵥ v =
      φ (fun a => v (oe (.inl a))) • oVec oe b₂ 0 +
        (v (oe (.inr (.inl 1))) + v (oe (.inr (.inr 1)))) •
          oVec oe 0 (uE (.inl 1) + uE (.inr 1)) := fun v => by
    rw [hX, oblk_mulVec_eq, hs₂, swapOneMat_sub_one_mulVec, smul_oVec, smul_oVec, oVec_add,
      smul_zero, smul_zero, add_zero, zero_add]
  have hli : ∀ a b : K, a • oVec oe b₂ (0 : Fin 2 ⊕ Fin 2 → K) +
      b • oVec oe 0 (uE (.inl 1) + uE (.inr 1)) = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    rw [smul_oVec, smul_oVec, oVec_add, smul_zero, smul_zero, add_zero, zero_add,
      ← oVec_zero (oe := oe)] at hab
    have e₂ : a • b₂ = 0 := by
      have := congrArg (fun v : ι → K => fun a => v (oe (.inl a))) hab
      simpa only [oVec_inl] using this
    have e₁ : b • (uE (.inl 1) + uE (.inr 1) : Fin 2 ⊕ Fin 2 → K) = 0 := by
      have := congrArg (fun v : ι → K => fun b => v (oe (.inr b))) hab
      simpa only [oVec_inr] using this
    refine ⟨(smul_eq_zero.mp e₂).resolve_right hb₂, ?_⟩
    have := congrFun e₁ (.inl 1)
    simpa [uE] using this
  have hφ0 : φ 0 = 0 := by
    have h := hs₂ 0
    rw [mulVec_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hb₂
  rw [commRank]
  refine rank_eq_two_of hli (fun v => ⟨_, _, hv v⟩) ⟨oVec oe w₁ 0, ?_⟩
    ⟨oVec oe 0 (uE (.inl 1)), ?_⟩
  · rw [hv, oVec_inl, hw₁, one_smul, oVec_apply_inr, oVec_apply_inr]
    simp
  · rw [hv, oVec_inl, oVec_apply_inr, oVec_apply_inr, hφ0]
    simp [uE]

end Rank

theorem oProj_conj {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : (ι → K) → K} (g h : StatedOmega Q) :
    MulAut.conj (oProj Q g) (oProj Q h) = oProj Q (g * h * g⁻¹) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

section Conj

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b)))}
  {hSL : commutator SL(2, K) = ⊤} {s₂ : GL ι₂ K} (hs₂ : s₂ * s₂ = 1) {s₀ : StatedOmega Q}
  (hs₀ : (s₀ : GL ι K) = oblkGL oe (s₂, swapOneGL))
include hs₂ hs₀

omit [CharP K 2] in
theorem swap_mul_self : s₀ * s₀ = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, hs₀, ← map_mul, Prod.mk_mul_mk, hs₂, swapOneGL_mul_self]
  exact map_one _

omit [CharP K 2] in
theorem swap_inv : s₀⁻¹ = s₀ := inv_eq_of_mul_eq_one_right (swap_mul_self hs₂ hs₀)

omit [CharP K 2] hs₂ in
theorem coe_swap_mul (Y : Matrix ι₂ ι₂ K) (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    ((s₀ : GL ι K) : Matrix ι ι K) * oblk oe Y X * ((s₀ : GL ι K) : Matrix ι ι K) =
      oblk oe ((s₂ : Matrix ι₂ ι₂ K) * Y * (s₂ : Matrix ι₂ ι₂ K))
        (swapOneMat * X * swapOneMat) := by
  rw [hs₀, coe_oblkGL, oblk_mul, oblk_mul]
  rfl

theorem conj_oRhoTwo_swap (C : SL(2, K)) :
    s₀ * oRhoTwo oe hQ hSL C * s₀⁻¹ = oRhoOne oe hQ hSL C := by
  apply Subtype.ext
  apply Units.ext
  rw [swap_inv hs₂ hs₀]
  change ((s₀ : GL ι K) : Matrix ι ι K) * oblk oe 1 (rhoTwoMat C) * ((s₀ : GL ι K) : Matrix ι ι K) =
    oblk oe 1 (rhoOneMat C)
  rw [coe_swap_mul hs₀, Matrix.mul_one, ← Units.val_mul, hs₂, Units.val_one,
    swapOne_conj_rhoTwo]
  rfl

theorem conj_oRhoOne_swap (C : SL(2, K)) :
    s₀ * oRhoOne oe hQ hSL C * s₀⁻¹ = oRhoTwo oe hQ hSL C := by
  apply Subtype.ext
  apply Units.ext
  rw [swap_inv hs₂ hs₀]
  change ((s₀ : GL ι K) : Matrix ι ι K) * oblk oe 1 (rhoOneMat C) * ((s₀ : GL ι K) : Matrix ι ι K) =
    oblk oe 1 (rhoTwoMat C)
  rw [coe_swap_mul hs₀, Matrix.mul_one, ← Units.val_mul, hs₂, Units.val_one, rhoOneMat_eq_shape,
    swapOne_conj_rhoOne]

omit [CharP K 2] in
theorem conj_oKappa_swap (hiso : ∀ w, Q₂ ((s₂ : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w)
    (Z : StatedOmega Q₂) :
    s₀ * oKappa oe hQ Z * s₀⁻¹ = oKappa oe hQ ⟨_, conj_mem_statedOmega hiso Z.2⟩ := by
  apply Subtype.ext
  apply Units.ext
  rw [swap_inv hs₂ hs₀]
  change ((s₀ : GL ι K) : Matrix ι ι K) * oblk oe ((Z : GL ι₂ K) : Matrix ι₂ ι₂ K) 1 *
    ((s₀ : GL ι K) : Matrix ι ι K) = oblk oe ((s₂ * (Z : GL ι₂ K) * s₂⁻¹ : GL ι₂ K) :
      Matrix ι₂ ι₂ K) 1
  rw [coe_swap_mul hs₀, Matrix.mul_one, swapOneMat_mul_self, inv_eq_of_mul_eq_one_right hs₂,
    Units.val_mul, Units.val_mul]

theorem map_conj_oBarTwo_swap :
    (oBarTwo oe hQ hSL).map (MulAut.conj (oProj Q s₀)).toMonoidHom = oBarOne oe hQ hSL := by
  rw [oBarTwo, oBarOne, ← MonoidHom.range_comp]
  congr 1
  ext C
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [oProj_conj, conj_oRhoTwo_swap hs₂ hs₀]

theorem map_conj_oBarOne_swap :
    (oBarOne oe hQ hSL).map (MulAut.conj (oProj Q s₀)).toMonoidHom = oBarTwo oe hQ hSL := by
  rw [oBarTwo, oBarOne, ← MonoidHom.range_comp]
  congr 1
  ext C
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [oProj_conj, conj_oRhoOne_swap hs₂ hs₀]

omit [CharP K 2] in
theorem map_conj_oBarL_swap (hiso : ∀ w, Q₂ ((s₂ : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) :
    (oBarL oe hQ).map (MulAut.conj (oProj Q s₀)).toMonoidHom = oBarL oe hQ := by
  have hiso' : ∀ w, Q₂ (((s₂⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w := by
    rw [inv_eq_of_mul_eq_one_right hs₂]
    exact hiso
  apply le_antisymm
  · rintro _ ⟨_, ⟨Z, rfl⟩, rfl⟩
    refine ⟨⟨_, conj_mem_statedOmega hiso Z.2⟩, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [oProj_conj, conj_oKappa_swap hs₂ hs₀ hiso]
  · rintro _ ⟨Z, rfl⟩
    refine ⟨oProj Q (oKappa oe hQ ⟨_, conj_mem_statedOmega hiso' Z.2⟩), ⟨_, rfl⟩, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [oProj_conj, conj_oKappa_swap hs₂ hs₀ hiso]
    congr 2
    apply Subtype.ext
    simp only [inv_inv]
    rw [inv_eq_of_mul_eq_one_right hs₂]
    rw [show s₂ * (s₂ * (Z : GL ι₂ K) * s₂) * s₂ = (s₂ * s₂) * Z * (s₂ * s₂) by group, hs₂,
      one_mul, mul_one]

end Conj

end CFSG.ComponentClassification.RankTwoClassical
