module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22
public import CFSG.Monster.B.GSide.CompletionFusion
public import CFSG.Monster.B.CTIB.HInnerCensus
public import CFSG.Monster.B.GSide.NotTwoCentral
public import CFSG.Fischer.UnitaryAction
public import CFSG.LieType.Chevalley.TwistedE6FieldTwoRelativeData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Monster.B.TwoA.Census.CosetEnum
public import CFSG.Monster.Existence.Census.TrialityWitnesses
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Co1.Module.InvGroupBase
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate1003
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10069Base
public import Certificates.Certificate10070
public import Certificates.Certificate10070Base
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate110
public import Certificates.Certificate12
public import Certificates.Certificate16005
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.GSide CFSG.Monster.B.CTIB

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem inclusion_xhatEam
    : Subgroup.inclusion Eam_le_Shat xhatEam = xhatS :=
  Subtype.ext rfl

theorem inclusion_cE'_mul_xhatEam :
    Subgroup.inclusion Eam_le_Shat (cE' * xhatEam) = clabelS cw0 :=
  Subtype.ext (by
    rw [coe_clabelS, clabel_cw0]
    rfl)

theorem not_isConj_xhatEam
    : ¬ IsConj xhatEam (cE' * xhatEam) := by
  intro h
  have h' := rankS_conj ((Subgroup.inclusion Eam_le_Shat).map_isConj h)
  rw [inclusion_xhatEam, inclusion_cE'_mul_xhatEam, ← sEquiv_xs, rankS_sEquiv_xs] at h'
  have h2 : rankS (clabelS cw0) = 1860 := rank_clabelS cw0
  omega

theorem rkH_conj
    {y y' : vStab cv0} (h : IsConj y y') : rkH y = rkH y' :=
  rankS_conj ((vStab cv0).subtype.map_isConj h)

theorem isConj_cV0_mul
    {y y' : vStab cv0} (h : IsConj y y') : IsConj (cV0 * y) (cV0 * y') := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨g, ?_⟩
  have hc : g * cV0 = cV0 * g := cV0_comm g
  calc g * (cV0 * y) * g⁻¹ = g * cV0 * y * g⁻¹ := by group
    _ = cV0 * (g * y * g⁻¹) := by rw [hc]; group

theorem isConj_of_isConj_vStabEam
    {y w : vStab cv0} (h : IsConj (vStabEam y) (vStabEam w)) :
    IsConj y w := by
  have h' := vStabEam.symm.toMonoidHom.map_isConj h
  simpa using h'

theorem mem_commutator_of_rkH
    {y : vStab cv0} (hy2 : y * y = 1) (h1 : rkH y ≠ 2158)
    (h2 : rkH (cV0 * y) ≠ 2158) : y ∈ commutator (vStab cv0) := by
  by_contra hy
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  obtain ⟨-, -, b, x, -, -, -, -, -, -, -, -, -, -, -, -, hcl1, hcl2, -, -, -, -, -, hrcb, -,
    hrcbx, -⟩ := native_H_outer_involution_classes hρ
  have hy' : vStabEam y ∉ commutator Eam := by
    rw [← map_commutator_vStabEam]
    intro h
    obtain ⟨w, hw, hwy⟩ := h
    exact hy (by rwa [vStabEam.injective hwy] at hw)
  have hy2' : vStabEam y * vStabEam y = 1 := by rw [← map_mul, hy2, map_one]
  have hcb : rkH (cV0 * b) = 2158 := hrcb
  have hcbx : rkH (cV0 * (b * x)) = 2158 := hrcbx
  rcases isConj_of_outer_involution hρ hcl1 hcl2 hy' hy2' with (h | h) | (h | h)
  · exact h2 ((rkH_conj (isConj_cV0_mul (isConj_of_isConj_vStabEam h))).trans hcb)
  · exact h1 ((rkH_conj (isConj_of_isConj_vStabEam h)).trans hcb)
  · exact h2 ((rkH_conj (isConj_cV0_mul (isConj_of_isConj_vStabEam h))).trans hcbx)
  · exact h1 ((rkH_conj (isConj_of_isConj_vStabEam h)).trans hcbx)

theorem cV0_mem_commutator' :
    cV0 ∈ commutator (vStab cv0) := by
  have h : vStabEam cV0 ∈ commutator Eam := by rw [vStabEam_cV0]; exact cE'_mem_commutator
  rw [← map_commutator_vStabEam] at h
  obtain ⟨w, hw, hwy⟩ := h
  rwa [vStabEam.injective hwy] at hw

theorem coe_sEquiv_inv
    (s : Sbp) : ((sEquiv s⁻¹ : Shat) : Dfull) = ((toShat s : Shat) : Dfull) := by
  rw [CFSG.Monster.B.CTIB.coe_sEquiv]
  simp [toShat]

theorem labelS_mem_Qs
    : labelS ∈ Qs := qS_mem_Qs_of_mem_jClass labelS_mem_jClass

theorem exists_mem_NH_of_mem_centQ
    {s : Sbp} (hsQ : s ∈ Qs) (hsc : s * labelS = labelS * s) :
    ∃ y : vStab cv0, y ∈ NH ∧ (y : Shat) = sEquiv s := by
  refine ⟨⟨sEquiv s, (commute_labelS_iff_mem s).1 hsc⟩, ?_, rfl⟩
  have hinv : s⁻¹ ∈ {y | y ∈ Qs ∧ y * labelS = labelS * y} := by
    refine ⟨inv_mem hsQ, ?_⟩
    calc s⁻¹ * labelS = s⁻¹ * (labelS * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * labelS) * s⁻¹ := by rw [hsc]
      _ = labelS * s⁻¹ := by group
  have h := Set.mem_image_of_mem (fun y : Sbp => ((toShat y : Shat) : Dfull)) hinv
  rw [image_centQ_labelS] at h
  have e := coe_sEquiv_inv s⁻¹
  rw [inv_inv] at e
  show iotaH _ ∈ Sp8.N1
  rw [iotaH_apply]
  exact e ▸ h

theorem symm_mem_centQ_of_mem_NH
    {y : vStab cv0} (hy : y ∈ NH) :
    sEquiv.symm (y : Shat) ∈ Qs ∧
      sEquiv.symm (y : Shat) * labelS = labelS * sEquiv.symm (y : Shat) := by
  have h : iotaH y ∈ (Sp8.N1 : Set Dfull) := hy
  rw [← image_centQ_labelS] at h
  obtain ⟨s, ⟨hsQ, hsc⟩, hs⟩ := h
  have e : sEquiv.symm (y : Shat) = s⁻¹ := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [coe_sEquiv_inv]
    exact (hs.trans (iotaH_apply y)).symm
  rw [e]
  refine ⟨inv_mem hsQ, ?_⟩
  calc s⁻¹ * labelS = s⁻¹ * (labelS * s) * s⁻¹ := by group
    _ = s⁻¹ * (s * labelS) * s⁻¹ := by rw [hsc]
    _ = labelS * s⁻¹ := by group

theorem mem_commutator_of_mem_NH_of_mul_self
    {y : vStab cv0} (hy : y ∈ NH) (hy2 : y * y = 1) :
    y ∈ commutator (vStab cv0) := by
  by_cases h1 : y = 1
  · rw [h1]; exact one_mem _
  by_cases hc : y = cV0
  · rw [hc]; exact cV0_mem_commutator'
  obtain ⟨hsQ, hsc⟩ := symm_mem_centQ_of_mem_NH hy
  set s := sEquiv.symm (y : Shat) with hsdef
  have hs2 : s * s = 1 := by
    rw [hsdef, ← map_mul, ← Subgroup.coe_mul, hy2, Subgroup.coe_one, map_one]
  have hs1 : s ≠ 1 := fun h => h1 (by
    have : (y : Shat) = 1 := by rw [← sEquiv.apply_symm_apply (y : Shat), ← hsdef, h, map_one]
    exact Subtype.ext this)
  have hsc' : s ≠ labelS := fun h => hc (by
    have : (y : Shat) = cV0 := by
      rw [← sEquiv.apply_symm_apply (y : Shat), ← hsdef, h, ← sEquiv_symm_cV0,
        MulEquiv.apply_symm_apply]
    exact Subtype.ext this)
  obtain ⟨-, hr, -⟩ := native_inner_involution_census labelS_mem_Qs (IsConj.refl labelS)
  have hpair := hr s hsQ hsc hs2 hs1 hsc'
  have e1 : rkH y = ((βr s) - 1).rank := rfl
  have e2 : rkH (cV0 * y) = ((βr (labelS * s)) - 1).rank := by
    rw [rkH, Subgroup.coe_mul, map_mul, sEquiv_symm_cV0]
  have k1 : rkH y ≠ 2158 := by
    rw [e1]
    rcases hpair with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have k2 : rkH (cV0 * y) ≠ 2158 := by
    rw [e2]
    rcases hpair with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> decide
  exact mem_commutator_of_rkH hy2 k1 k2

theorem NH_le_commutator :
    NH ≤ commutator (vStab cv0) := by
  have : Finite (vStab cv0) := Nat.finite_of_card_ne_zero (by rw [natCard_H]; norm_num)
  by_contra hle
  have hrel : (commutator (vStab cv0)).relIndex NH = 2 := by
    have h1 : (commutator (vStab cv0)).relIndex NH ≠ 1 := fun h => hle (relIndex_eq_one.1 h)
    have h2 : (commutator (vStab cv0)).relIndex NH ≤ 2 := by
      have h := relIndex_le_of_le_right (H := commutator (vStab cv0)) (le_top : NH ≤ ⊤)
        (by rw [relIndex_top_right, index_commutator_vStab_cv0]; norm_num)
      rwa [relIndex_top_right, index_commutator_vStab_cv0] at h
    have h0 : (commutator (vStab cv0)).relIndex NH ≠ 0 := by
      intro h
      have e := relIndex_mul_card (commutator (vStab cv0)) NH
      rw [h, zero_mul, natCard_NH] at e
      norm_num at e
    omega
  have hcardKN : Nat.card (commutator (vStab cv0) ⊓ NH : Subgroup (vStab cv0)) = 2 ^ 21 := by
    have e := relIndex_mul_card (commutator (vStab cv0)) NH
    rw [hrel, natCard_NH] at e
    omega
  obtain ⟨hA, -, -, -, -, -, -, hB, -, -⟩ :=
    native_inner_involution_census labelS_mem_Qs (IsConj.refl labelS)
  have hBA : {y | y ∈ Qs ∧ y * labelS = labelS * y ∧ y * y ≠ 1} ⊆
      {y | y ∈ Qs ∧ y * labelS = labelS * y} := fun y hy => ⟨hy.1, hy.2.1⟩
  have hA₁ : ({y | y ∈ Qs ∧ y * labelS = labelS * y} \
      {y | y ∈ Qs ∧ y * labelS = labelS * y ∧ y * y ≠ 1}).ncard = 2 ^ 22 - 2095104 := by
    rw [Set.ncard_sdiff hBA, hA, hB]
  have hmap : (fun s => (sEquiv s : Shat)) '' ({y | y ∈ Qs ∧ y * labelS = labelS * y} \
      {y | y ∈ Qs ∧ y * labelS = labelS * y ∧ y * y ≠ 1}) ⊆
      (((commutator (vStab cv0) ⊓ NH).map (vStab cv0).subtype : Subgroup Shat) : Set Shat) := by
    rintro _ ⟨s, ⟨⟨hsQ, hsc⟩, hs2⟩, rfl⟩
    have hs2' : s * s = 1 := by
      by_contra h
      exact hs2 ⟨hsQ, hsc, h⟩
    obtain ⟨y, hyN, hys⟩ := exists_mem_NH_of_mem_centQ hsQ hsc
    have hy2 : y * y = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hys, ← map_mul, hs2', map_one,
      Subgroup.coe_one])
    exact ⟨y, ⟨mem_commutator_of_mem_NH_of_mul_self hyN hy2, hyN⟩, hys⟩
  have h := Set.ncard_le_ncard hmap
  rw [Set.ncard_image_of_injective _ sEquiv.injective, hA₁, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, card_map_of_injective (vStab cv0).subtype_injective, hcardKN] at h
  norm_num at h

theorem vStabEam_lamW0H
    : vStabEam lamW0H = cE' * xhatEam := by
  rw [← vStabEam_cV0_mul_lamW0H, map_mul, vStabEam_cV0, ← mul_assoc]
  have h : cE' * cE' = 1 := by rw [← pow_two, ← orderOf_cE', pow_orderOf_eq_one]
  rw [h, one_mul]

theorem natCard_commutator_Eam_eq
    : Nat.card (commutator Eam) = 2 ^ 37 * 1113694156575 := by
  rw [short_F4_derived_standard_perfect_cover.2.2.2.2.2.2.2.1]
  norm_num

theorem natCard_commutator_vStab
    : Nat.card (commutator (vStab cv0)) = 2 ^ 37 * 1113694156575 := by
  rw [← natCard_commutator_Eam_eq, ← map_commutator_vStabEam,
    card_map_of_injective vStabEam.injective]

theorem eq_four_of_centralizes
    {T : Subgroup (vStab cv0)} (hNT : NH ≤ T) {b : vStab cv0}
    (hb : ∀ y ∈ T, y * b = b * y) :
    b = 1 ∨ b = cV0 ∨ b = lamW0H ∨ b = cV0 * lamW0H := by
  have hx : b * (cV0 * lamW0H) = cV0 * lamW0H * b :=
    (hb _ (hNT (mul_mem cV0_mem_NH lamW0H_mem_NH))).symm
  have hP : iotaH b ∈ Sp8.P1 := by
    show iotaH b ∈ Jhat ⊓ Subgroup.centralizer {Sp8.cQ}
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [← centralizer_xhat, mem_centralizer_singleton_iff, ← iotaH_cV0_mul_lamW0H]
      exact (map_mul iotaH _ _).symm.trans ((congrArg iotaH hx).trans (map_mul iotaH _ _))
    · rw [mem_centralizer_singleton_iff, ← iotaH_cV0]
      exact (map_mul iotaH _ _).symm.trans ((congrArg iotaH (cV0_comm b)).trans
        (map_mul iotaH _ _))
  exact eq_four_of_iotaH_mem (mem_closure_of_centralizer_N1 hP (iotaH_comm_N1 hNT hb))

@[expose] noncomputable def sylowE'
    (T₀ : Subgroup (vStab cv0)) : Subgroup (commutator Eam) :=
  ((commutator (vStab cv0) ⊓ T₀).map vStabEam.toMonoidHom).subgroupOf (commutator Eam)

theorem map_inf_le_commutator
    (T₀ : Subgroup (vStab cv0)) :
    (commutator (vStab cv0) ⊓ T₀).map vStabEam.toMonoidHom ≤ commutator Eam := by
  rw [← map_commutator_vStabEam]
  exact map_mono inf_le_left

theorem mem_sylowE'_iff
    (T₀ : Subgroup (vStab cv0)) (t : commutator Eam) :
    t ∈ sylowE' T₀ ↔ vStabEam.symm (t : Eam) ∈ commutator (vStab cv0) ⊓ T₀ := by
  rw [sylowE', mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hyt⟩
    have : vStabEam.symm (t : Eam) = y := by rw [← hyt]; simp
    rwa [this]
  · intro h
    exact ⟨_, h, by simp⟩

theorem natCard_sylowE'
    {T₀ : Sylow 2 (vStab cv0)}
    (h : Nat.card (commutator (vStab cv0) ⊓ (T₀ : Subgroup (vStab cv0)) : Subgroup (vStab cv0)) =
      2 ^ 37) :
    Nat.card (sylowE' (T₀ : Subgroup (vStab cv0))) =
      2 ^ (Nat.card (commutator Eam)).factorization 2 := by
  rw [sylowE', Nat.card_congr (subgroupOfEquivOfLe (map_inf_le_commutator _)).toEquiv,
    card_map_of_injective vStabEam.injective, h, natCard_commutator_Eam_eq,
    factorization_two_mul (by decide)]

theorem natCard_inf_sylow
    (T₀ : Sylow 2 (vStab cv0)) :
    Nat.card (commutator (vStab cv0) ⊓ (T₀ : Subgroup (vStab cv0)) : Subgroup (vStab cv0)) =
      2 ^ 37 := by
  have hrel : (commutator (vStab cv0)).relIndex (T₀ : Subgroup (vStab cv0)) = 2 := by
    have h1 : (commutator (vStab cv0)).relIndex (T₀ : Subgroup (vStab cv0)) ≠ 1 := by
      intro h
      have hd := card_dvd_of_le (relIndex_eq_one.1 h)
      rw [natCard_sylow_two_H, natCard_commutator_vStab] at hd
      norm_num at hd
    have h2 : (commutator (vStab cv0)).relIndex (T₀ : Subgroup (vStab cv0)) ≤ 2 := by
      have h := relIndex_le_of_le_right (H := commutator (vStab cv0))
        (le_top : (T₀ : Subgroup (vStab cv0)) ≤ ⊤)
        (by rw [relIndex_top_right, index_commutator_vStab_cv0]; norm_num)
      rwa [relIndex_top_right, index_commutator_vStab_cv0] at h
    have h0 : (commutator (vStab cv0)).relIndex (T₀ : Subgroup (vStab cv0)) ≠ 0 := by
      intro h
      have e := relIndex_mul_card (commutator (vStab cv0)) (T₀ : Subgroup (vStab cv0))
      rw [h, zero_mul, natCard_sylow_two_H] at e
      norm_num at e
    omega
  have e := relIndex_mul_card (commutator (vStab cv0)) (T₀ : Subgroup (vStab cv0))
  rw [hrel, natCard_sylow_two_H] at e
  omega

theorem four_comm_of_le_AH
    {T₀ : Subgroup (vStab cv0)} (hTA : T₀ ≤ AH) {y : vStab cv0}
    (hy : y ∈ T₀) {b : Eam} (hb : b = 1 ∨ b = cE' ∨ b = xhatEam ∨ b = cE' * xhatEam) :
    b * vStabEam y = vStabEam y * b := by
  have hyA := hTA hy
  have key : ∀ w : vStab cv0, (w = 1 ∨ w = cV0 ∨ w = lamW0H ∨ w = cV0 * lamW0H) →
      vStabEam w * vStabEam y = vStabEam y * vStabEam w := by
    intro w hw
    rw [← map_mul, ← map_mul]
    congr 1
    rcases hw with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact (cV0_comm y).symm
    · exact (lamW0H_comm hyA).symm
    · rw [mul_assoc, ← lamW0H_comm hyA, ← mul_assoc, ← cV0_comm y, mul_assoc]
  rcases hb with h | h | h | h
  · rw [show b = vStabEam 1 from h.trans (map_one vStabEam).symm]
    exact key 1 (Or.inl rfl)
  · rw [show b = vStabEam cV0 from h.trans vStabEam_cV0.symm]
    exact key cV0 (Or.inr (Or.inl rfl))
  · rw [show b = vStabEam (cV0 * lamW0H) from h.trans vStabEam_cV0_mul_lamW0H.symm]
    exact key (cV0 * lamW0H) (Or.inr (Or.inr (Or.inr rfl)))
  · rw [show b = vStabEam lamW0H from h.trans vStabEam_lamW0H.symm]
    exact key lamW0H (Or.inr (Or.inr (Or.inl rfl)))

theorem rootSylowData :
    RootSylowData := by
  refine ⟨not_isConj_xhatEam, ?_⟩
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hNT, hTA⟩ := exists_sylow_two_AH
  refine ⟨Sylow.ofCard _ (natCard_sylowE' (natCard_inf_sylow T₀)), ?_,
    fun b => ⟨fun hb => ?_, fun hb t ht => ?_⟩⟩
  · show xD ∈ sylowE' (T₀ : Subgroup (vStab cv0))
    have e : vStabEam.symm ((xD : commutator Eam) : Eam) = cV0 * lamW0H :=
      (MulEquiv.symm_apply_eq _).2 vStabEam_cV0_mul_lamW0H.symm
    refine (mem_sylowE'_iff _ xD).2 ?_
    rw [e]
    exact ⟨mul_mem cV0_mem_commutator' lamW0H_mem_commutator,
      hNT (mul_mem cV0_mem_NH lamW0H_mem_NH)⟩
  · have hb' : ∀ y ∈ commutator (vStab cv0) ⊓ (T₀ : Subgroup (vStab cv0)),
        y * vStabEam.symm b = vStabEam.symm b * y := by
      intro y hy
      have hyT : (⟨vStabEam y, map_inf_le_commutator _ ⟨y, hy, by simp⟩⟩ : commutator Eam) ∈
          Sylow.ofCard _ (natCard_sylowE' (natCard_inf_sylow T₀)) := by
        show _ ∈ sylowE' (T₀ : Subgroup (vStab cv0))
        refine (mem_sylowE'_iff _ _).2 ?_
        rw [MulEquiv.symm_apply_apply]
        exact hy
      apply vStabEam.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (hb _ hyT).symm
    have e := (vStabEam.apply_symm_apply b).symm
    rcases eq_four_of_centralizes (le_inf NH_le_commutator hNT) hb' with h | h | h | h
    · exact Or.inl (e.trans ((congrArg vStabEam h).trans (map_one vStabEam)))
    · exact Or.inr (Or.inl (e.trans ((congrArg vStabEam h).trans vStabEam_cV0)))
    · exact Or.inr (Or.inr (Or.inr (e.trans ((congrArg vStabEam h).trans vStabEam_lamW0H))))
    · exact Or.inr (Or.inr (Or.inl (e.trans ((congrArg vStabEam h).trans
        vStabEam_cV0_mul_lamW0H))))
  · have ht' : vStabEam.symm (t : Eam) ∈ commutator (vStab cv0) ⊓ (T₀ : Subgroup (vStab cv0)) :=
      (mem_sylowE'_iff _ t).1 ht
    have h := four_comm_of_le_AH hTA ht'.2 hb
    rwa [MulEquiv.apply_symm_apply] at h

@[expose] noncomputable def NE
    : Subgroup Eam := NH.map vStabEam.toMonoidHom

@[expose] def InvolutionsIntoN1
    : Prop :=
  ∀ u : commutator Eam, u * u = 1 → ∃ g : Eam, g * (u : Eam) * g⁻¹ ∈ NE

@[expose] def N1DihedralTest :
    Prop :=
  ∀ y ∈ NE, y * y = 1 → y ≠ cE' → IsConj (cE' * xhatEam) y ∨
    ∃ i₁ ∈ commutator Eam, ∃ i₂ ∈ commutator Eam, i₁ * i₁ = 1 ∧ i₂ * i₂ = 1 ∧
      i₁ * i₂ * (i₁ * i₂) = y

section Dihedral

variable {M : Type*} [Group M]

theorem comm_sq_of_dihedral {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (h4 : a * b * (a * b) * (a * b * (a * b)) = 1) :
    a * (a * b * (a * b)) = a * b * (a * b) * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : (a * b * (a * b))⁻¹ = a * b * (a * b) := inv_eq_of_mul_eq_one_right h4
  have h2 : (a * b * (a * b))⁻¹ = b * a * (b * a) := by
    simp only [mul_inv_rev, ha', hb', mul_assoc]
  calc a * (a * b * (a * b)) = a * (b * a * (b * a)) := by rw [← h2, h1]
    _ = a * b * (a * b) * a := by rw [show b * a * (b * a) = b * a * b * a by group]; group

theorem isConj_symm_of {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a : A} {b : B}
    (h : IsConj (e a) b) : IsConj a (e.symm b) := by
  have h1 := e.symm.toMonoidHom.map_isConj h
  simpa using h1

theorem map_conj_eq {A B : Type*} [Group A] [Group B] (e : A ≃* B) (g a : A) :
    e (g * a * g⁻¹) = e g * e a * (e g)⁻¹ := by
  rw [map_mul, map_mul, map_inv]

theorem isConj_of_conj_mem {K : Subgroup M} {a b : K} {g : M} (hg : g ∈ K)
    (h : g * (a : M) * g⁻¹ = b) : IsConj a b :=
  isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simpa using h)⟩

theorem exists_mem_closure_of_dihedral {K : Subgroup M} [K.Normal] {u : K} (hu2 : u * u = 1)
    {g i₁ i₂ : M} (hi₁ : i₁ ∈ K) (hi₂ : i₂ ∈ K) (h₁ : i₁ * i₁ = 1) (h₂ : i₂ * i₂ = 1)
    (h₁₂ : i₁ * i₂ * (i₁ * i₂) = g * (u : M) * g⁻¹) :
    ∃ s ∈ closure {i : K | i * i = 1 ∧ i * u = u * i}, s * s = u := by
  have hj : ∀ {i : M}, i ∈ K → g⁻¹ * i * g ∈ K := fun hi => by
    have h' := ‹K.Normal›.conj_mem _ hi g⁻¹
    rwa [inv_inv] at h'
  obtain ⟨j₁, ej₁⟩ : ∃ j : K, (j : M) = g⁻¹ * i₁ * g := ⟨⟨_, hj hi₁⟩, rfl⟩
  obtain ⟨j₂, ej₂⟩ : ∃ j : K, (j : M) = g⁻¹ * i₂ * g := ⟨⟨_, hj hi₂⟩, rfl⟩
  have hj₁ : j₁ * j₁ = 1 := Subtype.ext (by
    rw [coe_mul, ej₁, coe_one]
    calc g⁻¹ * i₁ * g * (g⁻¹ * i₁ * g) = g⁻¹ * (i₁ * i₁) * g := by group
      _ = 1 := by rw [h₁]; group)
  have hj₂ : j₂ * j₂ = 1 := Subtype.ext (by
    rw [coe_mul, ej₂, coe_one]
    calc g⁻¹ * i₂ * g * (g⁻¹ * i₂ * g) = g⁻¹ * (i₂ * i₂) * g := by group
      _ = 1 := by rw [h₂]; group)
  have hsu : j₁ * j₂ * (j₁ * j₂) = u := Subtype.ext (by
    rw [coe_mul, coe_mul, ej₁, ej₂]
    calc g⁻¹ * i₁ * g * (g⁻¹ * i₂ * g) * (g⁻¹ * i₁ * g * (g⁻¹ * i₂ * g)) =
        g⁻¹ * (i₁ * i₂ * (i₁ * i₂)) * g := by group
      _ = (u : M) := by rw [h₁₂]; group)
  have hu4 : j₁ * j₂ * (j₁ * j₂) * (j₁ * j₂ * (j₁ * j₂)) = 1 := by rw [hsu, hu2]
  have hc₁ := comm_sq_of_dihedral hj₁ hj₂ hu4
  have hj₂' : j₂ * j₁ = (j₁ * j₂)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hj₁, inv_eq_of_mul_eq_one_right hj₂]
  have hsq : j₂ * j₁ * (j₂ * j₁) = u := by
    rw [hj₂', ← mul_inv_rev, hsu, inv_eq_of_mul_eq_one_right hu2]
  have hu4' : j₂ * j₁ * (j₂ * j₁) * (j₂ * j₁ * (j₂ * j₁)) = 1 := by rw [hsq, hu2]
  have hc₂ := comm_sq_of_dihedral hj₂ hj₁ hu4'
  rw [hsq] at hc₂
  rw [hsu] at hc₁
  exact ⟨j₁ * j₂, mul_mem (subset_closure ⟨hj₁, hc₁⟩) (subset_closure ⟨hj₂, hc₂⟩), hsu⟩

end Dihedral

theorem exists_outer_comm_mem_RA :
    ∃ b lz : vStab cv0, b ∉ commutator (vStab cv0) ∧ lz ∈ RA ∧ b * lz = lz * b := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  obtain ⟨_u, z, b, x, -, hz, -, -, hx, -, hbx, -, hρb, -⟩ :=
    native_H_outer_involution_classes hρ
  have hb : b ∉ commutator (vStab cv0) := fun h =>
    not_mem_derivedStab_of_eq_beta hρ.1 hρb ((coe_mem_derivedStab_iff b).2 h)
  have hlzH : clabelS z ∈ vStab cv0 := clabelS_mem_vStab_cv0_of_adj hz
  refine ⟨b, ⟨clabelS z, hlzH⟩, hb, ⟨z, hz, rfl⟩, ?_⟩
  have hlzx : (⟨clabelS z, hlzH⟩ : vStab cv0) = cV0 * x := Subtype.ext (by
    rw [Subgroup.coe_mul, hx, coe_cV0, ← mul_assoc, clabelS_mul_clabelS, one_mul])
  rw [hlzx]
  calc b * (cV0 * x) = b * cV0 * x := by group
    _ = cV0 * (b * x) := by rw [cV0_comm b]; group
    _ = cV0 * x * b := by rw [hbx.eq]; group

theorem exists_mem_commutator_conj_of_comm
    {b lz : vStab cv0} (hb : b ∉ commutator (vStab cv0))
    (hlz : lz ∈ RA) (hblz : b * lz = lz * b) {y : vStab cv0} (hy : y ∈ RA) :
    ∃ g ∈ commutator (vStab cv0), g * lz * g⁻¹ = y := by
  have h1 : IsConj lamW0H lz := (mem_RA_iff_isConj _).1 hlz
  have h2 : IsConj lamW0H y := (mem_RA_iff_isConj _).1 hy
  obtain ⟨h, hh⟩ := isConj_iff.1 (h1.symm.trans h2)
  by_cases hK : h ∈ commutator (vStab cv0)
  · exact ⟨h, hK, hh⟩
  · refine ⟨h * b, (mul_mem_iff_of_index_two index_commutator_vStab_cv0).2
      (iff_of_false hK hb), ?_⟩
    calc h * b * lz * (h * b)⁻¹ = h * (b * lz * b⁻¹) * h⁻¹ := by group
      _ = h * lz * h⁻¹ := by rw [hblz, mul_inv_cancel_right]
      _ = y := hh

theorem exists_mem_commutator_conj_of_mem_RA
    {y : vStab cv0} (hy : y ∈ RA) :
    ∃ g ∈ commutator (vStab cv0), g * lamW0H * g⁻¹ = y := by
  obtain ⟨b, lz, hb, hlz, hblz⟩ := exists_outer_comm_mem_RA
  obtain ⟨g₁, hg₁, e₁⟩ := exists_mem_commutator_conj_of_comm hb hlz hblz lamW0H_mem_RA
  obtain ⟨g₂, hg₂, e₂⟩ := exists_mem_commutator_conj_of_comm hb hlz hblz hy
  refine ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁), ?_⟩
  calc g₂ * g₁⁻¹ * lamW0H * (g₂ * g₁⁻¹)⁻¹ = g₂ * (g₁⁻¹ * lamW0H * g₁) * g₂⁻¹ := by group
    _ = g₂ * lz * g₂⁻¹ := by rw [← e₁]; group
    _ = y := e₂

theorem isConj_commutator_of_isConj
    {u : commutator Eam} (h : IsConj (cE' * xhatEam) (u : Eam)) :
    IsConj (cD * xD) u := by
  have h0 : IsConj (vStabEam lamW0H) (u : Eam) := by
    rw [vStabEam_lamW0H]
    exact h
  obtain ⟨g, hg, hgy⟩ :=
    exists_mem_commutator_conj_of_mem_RA ((mem_RA_iff_isConj _).2 (isConj_symm_of vStabEam h0))
  have hgE : vStabEam g ∈ commutator Eam := by
    rw [← map_commutator_vStabEam]
    exact mem_map_of_mem _ hg
  have h2 : vStabEam g * vStabEam lamW0H * (vStabEam g)⁻¹ = (u : Eam) :=
    (map_conj_eq vStabEam g lamW0H).symm.trans ((congrArg vStabEam hgy).trans
      (MulEquiv.apply_symm_apply _ _))
  have h4 : ((cD * xD : commutator Eam) : Eam) = vStabEam lamW0H := by
    rw [coe_mul, coe_cD, coe_xD, vStabEam_lamW0H]
  exact isConj_of_conj_mem hgE (by rw [h4]; exact h2)

theorem involutionSquareTest_of
    (h1 : InvolutionsIntoN1) (h2 : N1DihedralTest) :
    InvolutionSquareTest := by
  intro u hu2 huc
  obtain ⟨g, hg⟩ := h1 u hu2
  have hu2' : (u : Eam) * u = 1 := by rw [← coe_mul, hu2, coe_one]
  have hy2 : g * (u : Eam) * g⁻¹ * (g * (u : Eam) * g⁻¹) = 1 := by
    calc g * (u : Eam) * g⁻¹ * (g * (u : Eam) * g⁻¹) = g * ((u : Eam) * u) * g⁻¹ := by group
      _ = 1 := by rw [hu2']; group
  have hyc : g * (u : Eam) * g⁻¹ ≠ cE' := by
    intro h
    apply huc
    apply Subtype.ext
    rw [coe_cD]
    have hc : g * cE' = cE' * g := by
      have := (mem_center_iff.1 (short_F4_derived_standard_perfect_cover.2.2.1 ▸
        mem_zpowers cE' : cE' ∈ center Eam)) g
      exact this
    calc (u : Eam) = g⁻¹ * (g * (u : Eam) * g⁻¹) * g := by group
      _ = cE' := by rw [h, mul_assoc, ← hc, inv_mul_cancel_left]
  rcases h2 _ hg hy2 hyc with h | ⟨i₁, hi₁, i₂, hi₂, h₁, h₂, h₁₂⟩
  · left
    refine isConj_commutator_of_isConj (h.trans (isConj_iff.2 ⟨g⁻¹, ?_⟩))
    group
  · right
    have hN : (commutator Eam).Normal := by
      rw [_root_.commutator_def]
      infer_instance
    exact exists_mem_closure_of_dihedral hu2 hi₁ hi₂ h₁ h₂ h₁₂

theorem stroth22_of_cover
    (hO : CoverOuterLeTwo) (hT : InvolutionSquareTest) : Stroth22 :=
  stroth22_of_inputs hO hT rootSylowData

theorem stroth22_of_N1
    (hO : CoverOuterLeTwo) (h1 : InvolutionsIntoN1) (h2 : N1DihedralTest) :
    Stroth22 :=
  stroth22_of_cover hO (involutionSquareTest_of h1 h2)

end CFSG.EvenSmallLie.TwoE6
