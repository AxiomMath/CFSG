module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYDescent
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYExt
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.PartOne.KCOrthogonalSubfield

section Transport

theorem mulAut_conj_eq_of_congr_eq {M N : Type*} [Group M] [Group N] (Φ₁ Φ₂ : M ≃* N)
    {β F : MulAut M} {γ : MulAut N} (h₁ : MulAut.congr Φ₁ β = γ) (h₂ : MulAut.congr Φ₂ F = γ) :
    (Φ₁.trans Φ₂.symm : MulAut M) * β * (Φ₁.trans Φ₂.symm : MulAut M)⁻¹ = F := by
  have e₁ : ∀ y, Φ₁ (β y) = γ (Φ₁ y) := fun y => by
    rw [← h₁]
    change Φ₁ (β y) = Φ₁ (β (Φ₁.symm (Φ₁ y)))
    rw [MulEquiv.symm_apply_apply]
  have e₂ : ∀ y, Φ₂ (F y) = γ (Φ₂ y) := fun y => by
    rw [← h₂]
    change Φ₂ (F y) = Φ₂ (F (Φ₂.symm (Φ₂ y)))
    rw [MulEquiv.symm_apply_apply]
  apply MulEquiv.ext
  intro x
  change Φ₂.symm (Φ₁ (β (Φ₁.symm (Φ₂ x)))) = F x
  rw [e₁, MulEquiv.apply_symm_apply]
  apply Φ₂.injective
  rw [MulEquiv.apply_symm_apply, e₂]

theorem autExtensionComm_transport {A₁ A₂ M₁ M₂ : Type*} [Group A₁] [Group A₂] [Group M₁]
    [Group M₂] (Ξ : M₁ ≃* M₂) {θ₁ : MulAut M₁} {θ₂ : MulAut M₂} (hΞ : MulAut.congr Ξ θ₁ = θ₂)
    {j₁ : A₁ →* M₁} {j₂ : A₂ →* M₂} (e : A₁ ≃* A₂) (hj : ∀ a, Ξ (j₁ a) = j₂ (e a))
    (h : AutExtensionComm j₁ θ₁) : AutExtensionComm j₂ θ₂ := by
  intro δ
  obtain ⟨δ₁', hδ₁', hcomm⟩ := h (MulAut.congr e.symm δ)
  refine ⟨MulAut.congr Ξ δ₁', fun b => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective b
    change Ξ (δ₁' (Ξ.symm (j₂ (e a)))) = j₂ (δ (e a))
    rw [← hj, MulEquiv.symm_apply_apply, hδ₁', hj]
    change j₂ (e (e.symm (δ (e.symm.symm a)))) = j₂ (δ (e a))
    rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  · rw [← hΞ, ← map_mul, ← map_mul, hcomm]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_mulEquiv_congr_eq_fieldAutT_of_mulEquiv {σ : K ≃+* K} (hσ : orderOf σ = 2)
    {b c : K} (hb : σ b = b) (hc : σ c = c) (hirr : ∀ s : K, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {M : Type} [Group M] (Ξ₀ : M ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K))
    {F : MulAut M} (hFF : F * F = 1) {D : Subgroup (fixedSubgroup F)} (hD : CFSG.IsComponent D)
    {g : ℕ} (hDm : LieModel D .POmegaMinus 4 2 g) :
    ∃ Ξ : M ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c),
      MulAut.congr Ξ F = fieldAutT (coordinateQuadMinus 4 K (by norm_num) b c) σ
        (coordinateQuadMinus_fieldMap_of_fixed (by norm_num) hb hc) := by
  let eF := CatLeafProof.fixedSubgroupCongrEquiv Ξ₀ F
  have hF' : MulAut.congr Ξ₀ F * MulAut.congr Ξ₀ F = 1 := by rw [← map_mul, hFF, map_one]
  obtain ⟨Θ, hΘ⟩ := exists_mulEquiv_congr_eq_fieldAutT hσ hb hc hirr hF'
    (CFSG.LocalCores.isComponent_map_mulEquiv eF hD)
    (LieType.CurtisTits.lieModel_of_mulEquiv (D.equivMapOfInjective _ eF.injective) hDm)
  refine ⟨Ξ₀.trans Θ, ?_⟩
  rw [← hΘ]
  exact MulEquiv.ext fun _ => rfl

theorem involutionDescentComp_of_mulEquiv_omegaPlus8 {σ : K ≃+* K} (hσ : orderOf σ = 2)
    {b c : K} (hb : σ b = b) (hc : σ c = c) (hirr : ∀ s : K, σ s = s → s ^ 2 + b * s + c ≠ 0)
    {M : Type} [Group M] (Ξ₀ : M ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K))
    {F : MulAut M} (hFF : F * F = 1) {D : Subgroup (fixedSubgroup F)} (hD : CFSG.IsComponent D)
    {A : Type} [Group A] {g : ℕ} (hA : LieModel A .POmegaMinus 4 2 g) (eD : D ≃* A) :
    InvolutionDescentComp F A := by
  obtain ⟨ΞF, hΞF⟩ := exists_mulEquiv_congr_eq_fieldAutT_of_mulEquiv hσ hb hc hirr Ξ₀ hFF hD
    (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hA)
  intro β hββ ⟨C, hC, ⟨eC⟩⟩
  obtain ⟨Ξβ, hΞβ⟩ := exists_mulEquiv_congr_eq_fieldAutT_of_mulEquiv hσ hb hc hirr Ξ₀ hββ hC
    (LieType.CurtisTits.lieModel_of_mulEquiv eC.symm hA)
  exact ⟨_, mulAut_conj_eq_of_congr_eq Ξβ ΞF hΞβ hΞF⟩

end Transport

section ExtensionTransport

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem autExtensionComm_fixedSubgroup_of_congr_eq_fieldAutT {k : Subfield K} {σ : K ≃+* K}
    (hσk : ∀ x, x ∈ k ↔ σ x = x) (b c : k) (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (hQσ : ∀ v, coordinateQuadMinus 4 K (by norm_num) (b : K) (c : K)
      (coordinateFieldMap (2 * 4) σ v) =
        σ (coordinateQuadMinus 4 K (by norm_num) (b : K) (c : K) v))
    {M : Type} [Group M] {F : MulAut M}
    (Ξ : M ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) (b : K) (c : K)))
    (hΞ : MulAut.congr Ξ F = fieldAutT _ σ hQσ)
    (hperf : ⁅fixedSubgroup F, fixedSubgroup F⁆ = fixedSubgroup F) :
    AutExtensionComm (fixedSubgroup F).subtype F := by
  have hext := isExtension_coordinateQuadMinus k (by norm_num : 1 ≤ 4) b c
  have hΞF : ∀ x, Ξ (F x) = fieldAutT _ σ hQσ (Ξ x) := fun x => by
    rw [← hΞ]
    change Ξ (F x) = Ξ (F (Ξ.symm (Ξ x)))
    rw [MulEquiv.symm_apply_apply]
  have hfix : fixedSubgroup (fieldAutT _ σ hQσ) = (fixedSubgroup F).map Ξ.toMonoidHom := by
    rw [← hΞ, fixedSubgroup_mulAutCongr]
  have hQne : ∃ v, coordinateQuadMinus 4 K (by norm_num) (b : K) (c : K) v ≠ 0 := by
    obtain ⟨hQk, -⟩ := regular_coordinateQuadMinus 4 k b c le_rfl hirr
    obtain ⟨v, hv⟩ := exists_ne_zero_of_polar_nondegenerate (by norm_num : 1 ≤ 2 * 4) hQk
    refine ⟨vecIncl k v, ?_⟩
    rw [hext v]
    exact fun h => hv (Subtype.ext h)
  have hJ : (incl k hext).range = fixedSubgroup (fieldAutT _ σ hQσ) := by
    apply le_antisymm
    · intro t ht
      exact fieldAutT_fixes_J k _ σ hQσ hext hσk ht
    · have hperf' : ⁅fixedSubgroup (fieldAutT _ σ hQσ), fixedSubgroup (fieldAutT _ σ hQσ)⁆ =
          fixedSubgroup (fieldAutT _ σ hQσ) := by
        rw [hfix, ← Subgroup.map_commutator, hperf]
      have hle := E7Pilot.fixedSubgroup_fieldAutT_le hQσ hσk hext hQne
      calc fixedSubgroup (fieldAutT _ σ hQσ)
          = ⁅fixedSubgroup (fieldAutT _ σ hQσ), fixedSubgroup (fieldAutT _ σ hQσ)⁆ := hperf'.symm
        _ ≤ ⁅subfieldFixedGroup k _ _, subfieldFixedGroup k _ _⁆ := Subgroup.commutator_mono hle hle
        _ ≤ subfieldDerivedImage k hext := E7Pilot.commutator_subfieldFixedGroup_le hext
  have hinj := incl_injective k hext (by norm_num : 0 < 2 * 4)
  have hmem : ∀ a, Ξ.symm (incl k hext a) ∈ fixedSubgroup F := fun a => by
    change F (Ξ.symm (incl k hext a)) = Ξ.symm (incl k hext a)
    apply Ξ.injective
    rw [hΞF, MulEquiv.apply_symm_apply]
    exact fieldAutT_fixes_J k _ σ hQσ hext hσk ⟨a, rfl⟩
  let e₀ : matrixProjectiveDerived (coordinateQuadMinus 4 k (by norm_num) b c) →* fixedSubgroup F :=
    (Ξ.symm.toMonoidHom.comp (incl k hext)).codRestrict (fixedSubgroup F) hmem
  have he₀ : Function.Bijective e₀ := by
    refine ⟨fun a a' h => hinj (Ξ.symm.injective (congrArg Subtype.val h)), fun y => ?_⟩
    have hy : Ξ y ∈ fixedSubgroup (fieldAutT _ σ hQσ) := by
      change fieldAutT _ σ hQσ (Ξ y) = Ξ y
      rw [← hΞF]
      exact congrArg Ξ y.2
    rw [← hJ] at hy
    obtain ⟨a, ha⟩ := hy
    refine ⟨a, Subtype.ext ?_⟩
    change Ξ.symm (incl k hext a) = y
    rw [ha, MulEquiv.symm_apply_apply]
  have hΞ' : MulAut.congr Ξ.symm (fieldAutT _ σ hQσ) = F := by
    rw [← hΞ]
    exact MulEquiv.ext fun x => by
      change Ξ.symm (Ξ (F (Ξ.symm (Ξ.symm.symm x)))) = F x
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  exact autExtensionComm_transport Ξ.symm hΞ' (MulEquiv.ofBijective e₀ he₀) (fun _ => rfl)
    (autExtensionComm_incl_minus le_rfl hσk b c hirr hQσ)

end ExtensionTransport

section Y

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std

variable
  {f : ℕ} {K : Type} [Field K]

theorem isComponent_top_fixedSubgroup_d4LeviTwist (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    CFSG.IsComponent (⊤ : Subgroup (fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ)))) ∧
      Nonempty ((⊤ : Subgroup (fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ)))) ≃*
        (omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)) ∧
      LieModel ((omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD))
        .POmegaMinus 4 2 f ∧
      ⁅fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ)),
        fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ))⁆ =
          fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ)) := by
  have hfix := fixedSubgroup_d4LeviTwist hf hK hσ
  have hle : omegaMinusLevi σ ≤ subsystemGroup TwistTag.E6.tag K setD := inf_le_left
  have := isSimpleGroup_omegaMinusLevi hf hK hσ
  have := isPerfect_omegaMinusLevi hf hK hσ
  have hq : CFSG.IsQuasisimple ((omegaMinusLevi σ).subgroupOf
      (subsystemGroup TwistTag.E6.tag K setD)) := isQuasisimple_subgroupOf hle
  let eT : (⊤ : Subgroup (fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ)))) ≃*
      (omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD) :=
    Subgroup.topEquiv.trans (MulEquiv.subgroupCongr hfix)
  have hP : Group.IsPerfect ((omegaMinusLevi σ).subgroupOf
      (subsystemGroup TwistTag.E6.tag K setD)) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hle).symm.toMonoidHom)
      (subgroupOfEquivOfLe hle).symm.surjective
  refine ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eT.symm hq, Subgroup.IsSubnormal.top⟩, ⟨eT⟩,
    LieType.CurtisTits.lieModel_of_mulEquiv (subgroupOfEquivOfLe hle).symm
      (lieModel_omegaMinusLevi hf hK hσ), ?_⟩
  rw [hfix]
  exact Subgroup.isPerfect_iff.1 hP

theorem involutionDescentComp_d4LeviTwist (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    InvolutionDescentComp (d4LeviTwist (apply_apply_eq hK hσ))
      ((omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨hT, ⟨eT⟩, hA, -⟩ := isComponent_top_fixedSubgroup_d4LeviTwist hf hK hσ
  have hFF := levelTwist_mul_self (apply_apply_eq hK hσ) perm_mem_setD
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := apply_apply_eq hK hσ
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hω' : σE ω ≠ ω := hω
  have hord : orderOf σE = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact d4_sigma_mul_self hσσ) (d4_sigma_ne_one hω')
  have hirr : ∀ s : K, σE s = s → s ^ 2 + (ω + σE ω) * s + ω * σE ω ≠ 0 := by
    intro s hs h
    apply d4Minus_irr hσσ hω' ⟨s, mem_descentField.2 hs⟩
    apply Subtype.ext
    simpa [d4MinusB, d4MinusC] using h
  exact involutionDescentComp_of_mulEquiv_omegaPlus8 hord
    (mem_descentField.1 (add_self_mem_descentField hσσ ω))
    (mem_descentField.1 (mul_self_mem_descentField hσσ ω)) hirr
    (coordinatePlusWitnessEquiv K ((d4PsiEquiv K).trans (elementaryPlusStatedEquiv K))) hFF hT hA
    eT

theorem autExtensionComm_d4LeviTwist (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    AutExtensionComm ((omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)).subtype
      (d4LeviTwist (apply_apply_eq hK hσ)) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨hT, -, hA, hperf⟩ := isComponent_top_fixedSubgroup_d4LeviTwist hf hK hσ
  have hfix := fixedSubgroup_d4LeviTwist hf hK hσ
  have hFF := levelTwist_mul_self (apply_apply_eq hK hσ) perm_mem_setD
  rw [← hfix]
  obtain ⟨σE, rfl⟩ := exists_ringEquiv_toRingHom_eq σ
  have hσσ : ∀ c, σE (σE c) = c := apply_apply_eq hK hσ
  obtain ⟨ω, hω⟩ := exists_apply_ne hf hK hσ
  have hω' : σE ω ≠ ω := hω
  have hord : orderOf σE = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact d4_sigma_mul_self hσσ) (d4_sigma_ne_one hω')
  have hirr : ∀ s : K, σE s = s → s ^ 2 + (ω + σE ω) * s + ω * σE ω ≠ 0 := by
    intro s hs h
    apply d4Minus_irr hσσ hω' ⟨s, mem_descentField.2 hs⟩
    apply Subtype.ext
    simpa [d4MinusB, d4MinusC] using h
  have hTm : LieModel (⊤ : Subgroup (fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ))))
      .POmegaMinus 4 2 f := by
    obtain ⟨-, ⟨eT⟩, -, -⟩ := isComponent_top_fixedSubgroup_d4LeviTwist hf hK hσ
    exact LieType.CurtisTits.lieModel_of_mulEquiv eT.symm hA
  obtain ⟨Ξ, hΞ⟩ := exists_mulEquiv_congr_eq_fieldAutT_of_mulEquiv hord
    (mem_descentField.1 (add_self_mem_descentField hσσ ω))
    (mem_descentField.1 (mul_self_mem_descentField hσσ ω)) hirr
    (coordinatePlusWitnessEquiv K ((d4PsiEquiv K).trans (elementaryPlusStatedEquiv K))) hFF hT hTm
  exact autExtensionComm_fixedSubgroup_of_congr_eq_fieldAutT (k := descentField σE)
    (fun _ => mem_descentField) (d4MinusB hσσ ω) (d4MinusC hσσ ω) (d4Minus_irr hσσ hω') _ Ξ hΞ
    hperf

end Y

end CFSG.SeitzReduction.TwistedE6Pilot
