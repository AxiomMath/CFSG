module

public import CFSG.ClassicalInvolution.Q3.Q3TLBlock
public import CFSG.ClassicalInvolution.Q3.Q3TLLift
public import CFSG.ClassicalInvolution.Q3.Q3TLPos

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalInvolution.ModelFacts
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped MatrixGroups Pointwise

variable {K : Type} [Field K] [Finite K]

@[expose] def weylS : SL(2, K) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem eq_zero_of_det_eq_zero (hK : Nat.card K = 3) {m : Matrix (Fin 2) (Fin 2) K}
    (h1 : m.det = 0)
    (h2 : ((weylS : SL(2, K)) * m + m * (weylS : SL(2, K))).det = 0) : m = 0 := by
  have hsq : ∀ a b : K, a * a + b * b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases ha : a = 0
    · rw [ha, zero_mul, zero_add, mul_self_eq_zero] at hab
      exact ⟨ha, hab⟩
    · exfalso
      apply mul_self_ne_neg_one_of_card_three hK (b / a)
      field_simp
      linear_combination hab
  have hdet : ((weylS : SL(2, K)) * m + m * (weylS : SL(2, K))).det =
      (m 0 1 - m 1 0) * (m 0 1 - m 1 0) + (m 0 0 + m 1 1) * (m 0 0 + m 1 1) := by
    simp only [weylS, Matrix.det_fin_two, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [hdet] at h2
  obtain ⟨h3, h4⟩ := hsq _ _ h2
  rw [Matrix.det_fin_two] at h1
  have h5 : m 0 0 * m 0 0 + m 0 1 * m 0 1 = 0 := by
    linear_combination -h1 + (m 0 0) * h4 + (m 0 1) * h3
  obtain ⟨h6, h7⟩ := hsq _ _ h5
  have h8 : m 1 0 = 0 := by linear_combination -h3 + h7
  have h9 : m 1 1 = 0 := by linear_combination h4 - h6
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h6, h7, h8, h9]

section Block

variable {W W' : Submodule K (Fin 4 ⊕ Fin 4 → K)} (hc : IsCompl W W')
  (horth : ∀ u ∈ W, ∀ w ∈ W', polar (quadPlus 4 K) u w = 0)
  {P₁ P₂ : HypPair ((quadPlus 4 K).comp W.subtype)} (h : P₁.Orth P₂) (hdim : finrank K W = 4)

omit [Finite K] in
theorem thetaL_neg_one_apply (x : W) : thetaL h hdim (-1) x = -x := by
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  rw [thetaL_apply, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    neg_one_mul, map_neg]

omit [Finite K] in
theorem thetaR_neg_one_apply (x : W) : thetaR h hdim (-1) x = -x := by
  obtain ⟨m, rfl⟩ := coord_surjective h hdim x
  rw [thetaR_apply, inv_neg_one, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, mul_neg_one, map_neg]

omit [Finite K] in
theorem orthExtend_neg_apply {φ : W ≃ₗ[K] W} (hφ : ∀ x, φ x = -x)
    {G : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)} (hGW : ∀ u ∈ W, G u = u)
    (hGW' : ∀ w ∈ W', G w = -w) (x : Fin 4 ⊕ Fin 4 → K) : orthExtend hc φ x = -G x := by
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl' hc x
  have h1 := orthExtend_apply hc φ ⟨u, hu⟩ ⟨w, hw⟩
  simp only at h1
  rw [h1, hφ, map_add, hGW u hu, hGW' w hw, Submodule.coe_neg, neg_add, neg_neg]

omit [Finite K] in
theorem ePHom_eq_mk_of_eq_neg (g : StatedOmega (StatedQuadPlus 4 K))
    (b : elementaryGroup (quadPlus 4 K))
    (hb : ∀ x, (b : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) x =
      -toLinEquiv _ K g.val x) :
    ePHom K b = QuotientGroup.mk g := by
  rw [ePHom_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
  refine mem_scalars.mpr ⟨-1, fun v => ?_⟩
  have hv : (b : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) (-v) =
      toLinEquiv _ K g.val v := by rw [hb, map_neg, neg_neg]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, MulEquiv.apply_symm_apply,
    LinearEquiv.mul_apply, neg_one_smul]
  rw [← hv, LinearEquiv.inv_apply_apply']

omit [Finite K] in
theorem rhoL_neg_one (g : StatedOmega (StatedQuadPlus 4 K))
    (hGW : ∀ u ∈ W, toLinEquiv _ K g.val u = u) (hGW' : ∀ w ∈ W', toLinEquiv _ K g.val w = -w) :
    rhoL hc horth h hdim (-1) = QuotientGroup.mk g := by
  rw [rhoL_apply]
  refine ePHom_eq_mk_of_eq_neg g _ fun x => ?_
  rw [coe_blockHom]
  exact orthExtend_neg_apply hc (thetaL_neg_one_apply h hdim) hGW hGW' x

omit [Finite K] in
theorem rhoR_neg_one (g : StatedOmega (StatedQuadPlus 4 K))
    (hGW : ∀ u ∈ W, toLinEquiv _ K g.val u = u) (hGW' : ∀ w ∈ W', toLinEquiv _ K g.val w = -w) :
    rhoR hc horth h hdim (-1) = QuotientGroup.mk g := by
  rw [rhoR_apply]
  refine ePHom_eq_mk_of_eq_neg g _ fun x => ?_
  rw [coe_blockHom]
  exact orthExtend_neg_apply hc (thetaR_neg_one_apply h hdim) hGW hGW' x

omit [Finite K] in
theorem block_le_stabilizer {w : Fin 4 ⊕ Fin 4 → K} (hw : w ∈ W') :
    (rhoL hc horth h hdim).range ⊔ (rhoR hc horth h hdim).range ≤
      statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (K ∙ w) := by
  refine sup_le ?_ ?_
  · rintro _ ⟨A, rfl⟩
    change statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (rhoL hc horth h hdim A) (K ∙ w) =
      K ∙ w
    rw [rhoL_apply, ePHom_smul, coe_blockHom, Submodule.map_span, Set.image_singleton,
      LinearEquiv.coe_coe, orthExtend_apply_right hc _ hw]
  · rintro _ ⟨A, rfl⟩
    change statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (rhoR hc horth h hdim A) (K ∙ w) =
      K ∙ w
    rw [rhoR_apply, ePHom_smul, coe_blockHom, Submodule.map_span, Set.image_singleton,
      LinearEquiv.coe_coe, orthExtend_apply_right hc _ hw]

end Block

section Root

variable (hK : Nat.card K = 3) (g : StatedOmega (StatedQuadPlus 4 K))
  (hg2 : toLinEquiv _ K g.val * toLinEquiv _ K g.val = 1)
  (hc : IsCompl (plusSp (toLinEquiv _ K g.val)) (minusSp (toLinEquiv _ K g.val)))
  (horth : ∀ u ∈ plusSp (toLinEquiv _ K g.val), ∀ w ∈ minusSp (toLinEquiv _ K g.val),
    polar (quadPlus 4 K) u w = 0)
  {P₁ P₂ : HypPair ((quadPlus 4 K).comp (plusSp (toLinEquiv _ K g.val)).subtype)}
  (h : P₁.Orth P₂) (hdim : finrank K (plusSp (toLinEquiv _ K g.val)) = 4)

include hK hg2 in
theorem not_fixFam_solid_block :
    ¬ FixFam (conjugacyFamily
      (statedProjectiveSubspaceStabilizer (StatedQuadPlus 4 K) (flag 4 K 4)))
      ((rhoL hc horth h hdim).range ⊔ (rhoR hc horth h hdim).range) := by
  intro hX
  obtain ⟨S, hS, hle⟩ := exists_of_fixFam_solid hX
  obtain ⟨-, h2⟩ := three_eq_zero_two_ne_zero_of_card_eq_three hK
  have hGO := toLinEquiv_mem_orthogonalGroup g.2
  have hQ := nondegenerate_polarBilin_quadPlus 4 K
  have hgN : (QuotientGroup.mk g : StatedProj (StatedOmega (StatedQuadPlus 4 K))) ∈
      (rhoL hc horth h hdim).range ⊔ (rhoR hc horth h hdim).range :=
    Subgroup.mem_sup_left ⟨-1, rhoL_neg_one hc horth h hdim g (fun u hu => mem_plusSp.mp hu)
      (fun w hw => mem_minusSp.mp hw)⟩
  have htS := (mk_mem_stabilizer_iff g S).mp (hle hgN)
  have hSG : ∀ v ∈ S, toLinEquiv _ K g.val v ∈ S := fun v hv => by
    rw [← htS]
    exact ⟨v, hv, rfl⟩
  obtain ⟨ha, -⟩ := two_mul_finrank_inf_eq hQ h2 hGO hg2 hSG hS.2
    (by rw [hS.1, finrank_plusEight])
  have hne : S ⊓ plusSp (toLinEquiv _ K g.val) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at ha
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨m, hm⟩ := coord_surjective h hdim ⟨x, hx.2⟩
  have hinvL : ∀ A (y : plusSp (toLinEquiv _ K g.val)), (y : Fin 4 ⊕ Fin 4 → K) ∈ S →
      (thetaL h hdim A y : Fin 4 ⊕ Fin 4 → K) ∈ S := by
    intro A y hy
    have hst := hle (Subgroup.mem_sup_left ⟨A, rfl⟩ :
      rhoL hc horth h hdim A ∈ (rhoL hc horth h hdim).range ⊔ (rhoR hc horth h hdim).range)
    change statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (rhoL hc horth h hdim A) S = S
      at hst
    rw [rhoL_apply, ePHom_smul, coe_blockHom] at hst
    rw [← hst]
    refine ⟨y, hy, ?_⟩
    have := orthExtend_apply hc (thetaL h hdim A) y 0
    simpa using this
  have hinvR : ∀ B (y : plusSp (toLinEquiv _ K g.val)), (y : Fin 4 ⊕ Fin 4 → K) ∈ S →
      (thetaR h hdim B y : Fin 4 ⊕ Fin 4 → K) ∈ S := by
    intro B y hy
    have hst := hle (Subgroup.mem_sup_right ⟨B, rfl⟩ :
      rhoR hc horth h hdim B ∈ (rhoL hc horth h hdim).range ⊔ (rhoR hc horth h hdim).range)
    change statedProjectiveSubspaceAction (StatedQuadPlus 4 K) (rhoR hc horth h hdim B) S = S
      at hst
    rw [rhoR_apply, ePHom_smul, coe_blockHom] at hst
    rw [← hst]
    refine ⟨y, hy, ?_⟩
    have := orthExtend_apply hc (thetaR h hdim B) y 0
    simpa using this
  have hy₁ : ((coord P₁ P₂ ((weylS : SL(2, K)) * m) : plusSp (toLinEquiv _ K g.val)) :
      Fin 4 ⊕ Fin 4 → K) ∈ S := by
    rw [← thetaL_apply h hdim weylS m, hm]
    exact hinvL _ _ hx.1
  have hy₂ : ((coord P₁ P₂ (m * (weylS : SL(2, K))) : plusSp (toLinEquiv _ K g.val)) :
      Fin 4 ⊕ Fin 4 → K) ∈ S := by
    have := hinvR weylS⁻¹ ⟨x, hx.2⟩ hx.1
    rwa [← hm, thetaR_apply, inv_inv] at this
  have hdet1 : m.det = 0 := by
    rw [← map_coord h m, hm]
    exact hS.2 x hx.1
  have hdet2 : ((weylS : SL(2, K)) * m + m * (weylS : SL(2, K))).det = 0 := by
    rw [← map_coord h]
    refine hS.2 _ ?_
    rw [map_add, map_add]
    exact S.add_mem hy₁ hy₂
  have hm0 := eq_zero_of_det_eq_zero hK hdet1 hdet2
  rw [hm0, map_zero] at hm
  exact hx0 (congrArg Subtype.val hm).symm

include hK hg2 in
theorem smul_eq_of_fix_block {w : Fin 4 ⊕ Fin 4 → K} (hw : w ∈ minusSp (toLinEquiv _ K g.val))
    (hw0 : w ≠ 0) (hwQ : quadPlus 4 K w = 0)
    (α : MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K)))) (hα : Odd (orderOf α))
    (hαL : ∀ A, α (rhoL hc horth h hdim A) = rhoL hc horth h hdim A)
    (hαR : ∀ B, α (rhoR hc horth h hdim B) = rhoR hc horth h hdim B) :
    α • statedPointFamily (coe_quadPlus 4 K) = statedPointFamily (coe_quadPlus 4 K) := by
  refine smul_eq_of_fixFam_point_odd α hα ?_
    (fixFam_point_of_le hw0 hwQ (block_le_stabilizer hc horth h hdim hw))
    (not_fixFam_solid_block hK g hg2 hc horth h hdim)
  rw [Subgroup.map_sup, MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  · congr 1
    exact MonoidHom.ext hαL
  · congr 1
    exact MonoidHom.ext hαR

end Root

end CFSG.ClassicalInvolution.Q3.Q3T
