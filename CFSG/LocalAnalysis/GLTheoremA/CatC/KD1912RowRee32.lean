module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PCore.SelfCentralizing
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4ElementCentralizer
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.Blueprint (suzukiGroup)

open CFSG.Blueprint.Chevalley (ModGL)

open CFSG.LieType.Chevalley (finite_modGL)

open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Dickson.SuzukiReeB
open CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


section Certificates


theorem pPrimeCore_five_reeGamma_zero {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) :
    CFSG.pPrimeCore 5 (ReeTag.F4.reeGamma k 0) = ⊥ := by
  classical
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  let e : ↥(reeFixed ReeTag.F4 k 0) ≃* ↥(ReeTag.F4.reeGamma k 0) :=
    ReeTag.reeFixedEquivReeGamma k 0
  let φ : ↥(ReeTag.F4.reeGamma k 0) →* ↥(reeFixed ReeTag.F4 k 0) := e.symm.toMonoidHom
  let N' : Subgroup ↥(reeFixed ReeTag.F4 k 0) := N.map φ
  have hN'n : N'.Normal := hN.map φ e.symm.surjective
  have hcard : Nat.card N' = Nat.card N := Subgroup.card_map_of_injective (f := φ) e.symm.injective
  haveI := hN'n
  rcases CFSG.LieType.Simplicity.eq_bot_or_sup_eq_top_of_card_eq_two hk N' with hbot | hsup
  · have h : N.map φ = ⊥ := hbot
    exact (Subgroup.map_eq_bot_iff_of_injective N e.symm.injective).1 h
  · exfalso
    have hP : IsPGroup 2 (↥(reeFixed ReeTag.F4 k 0) ⧸ N') :=
      CFSG.LieType.Simplicity.isPGroup_quotient_of_sup_eq_top hk N' hsup
    obtain ⟨j, hj⟩ := hP.exists_card_eq
    have hcardG : Nat.card N' * 2 ^ j = Nat.card ↥(reeFixed ReeTag.F4 k 0) := by
      rw [← hj, ← Subgroup.index_eq_card]
      exact Subgroup.card_mul_index N'
    have hΓ : Nat.card ↥(reeFixed ReeTag.F4 k 0) = 35942400 := by
      rw [Nat.card_congr e.toEquiv,
        (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
          0 k hk).1]
      norm_num
    have h5Γ : 5 ∣ Nat.card ↥(reeFixed ReeTag.F4 k 0) := by rw [hΓ]; norm_num
    rw [← hcardG] at h5Γ
    have h52 : Nat.Coprime 5 (2 ^ j) := (by norm_num : Nat.Coprime 5 2).pow_right j
    have h5 : 5 ∣ Nat.card N' := by
      rcases (Nat.prime_five.dvd_mul (m := Nat.card N') (n := 2 ^ j)).1 h5Γ with h | h
      · exact h
      · exact absurd h ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 h52)
    have hcop' : Nat.Coprime 5 (Nat.card N') := by rw [hcard]; exact hcop
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hcop') h5

theorem odd_card_gLAPPrimeCoreOf_fixSubgroup_conj_of_orderOf_five
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) {y : ↥(ReeTag.F4.reeGamma K 2)} (hy : orderOf y = 5) :
    Odd (Nat.card (GLAPPrimeCoreOf 5 (fixSubgroup (MulAut.conj y)))) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    omega
  have hEp : IsPGroup 5 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have hEel : CFSG.Open.IsElemAbelian 5 (Subgroup.zpowers y) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy5, one_zpow]
  obtain ⟨A, S, -, hAcard, -, hcomm, hAinf, hAsup, hScard, ⟨eS⟩, -, -, -⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.exists_centralizer_decomp hK P (Subgroup.zpowers y)
      hEP hEel y (Subgroup.mem_zpowers y) hy1
  have hfix : fixSubgroup (MulAut.conj y) =
      Subgroup.centralizer ({y} : Set ↥(ReeTag.F4.reeGamma K 2)) := fixSubgroup_conj y
  have hCeq : fixSubgroup (MulAut.conj y) = A ⊔ S := by rw [hfix, ← hAsup]
  have hSC : S ≤ fixSubgroup (MulAut.conj y) := by rw [hCeq]; exact le_sup_right
  have hAnorm : A ≤ Subgroup.normalizer (S : Set ↥(ReeTag.F4.reeGamma K 2)) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha s hs
    have h : a * s * a⁻¹ = s := by rw [hcomm a ha s hs]; group
    rw [h]
    exact hs
  have hSnormal : (S.subgroupOf (fixSubgroup (MulAut.conj y))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSC, hCeq]
    exact sup_le hAnorm (Subgroup.le_normalizer (H := S))
  have hcardC : Nat.card (fixSubgroup (MulAut.conj y)) = 25 * Nat.card S := by
    rw [hCeq, CFSG.HardMathSupport.Malle.LocalAction.card_sup_of_commute_of_inf_eq_bot hcomm
      hAinf, hAcard]
  have hrel : S.relIndex (fixSubgroup (MulAut.conj y)) = 25 := by
    have hmul : Nat.card S * S.relIndex (fixSubgroup (MulAut.conj y)) =
        Nat.card (fixSubgroup (MulAut.conj y)) := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
      exact Subgroup.card_mul_index (S.subgroupOf (fixSubgroup (MulAut.conj y)))
    rw [hcardC] at hmul
    exact Nat.mul_left_cancel Nat.card_pos (by rw [hmul, Nat.mul_comm])
  have hSbot : GLAPPrimeCoreOf 5 S = ⊥ := by
    rw [gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore]
    haveI : IsSimpleGroup ↥(suzukiGroup 2 K) :=
      (CFSG.LieType.Ree.suzuki_simple (a := 2) (by norm_num) hK).2.2
    haveI hSs : IsSimpleGroup ↥S := eS.isSimpleGroup
    have hdvd : 5 ∣ Nat.card ↥S := by rw [hScard]; norm_num
    exact gLAPPrimeCore_eq_bot_of_isSimpleGroup_of_dvd_card Nat.prime_five hSs hdvd
  have hCbot : GLAPPrimeCoreOf 5 (fixSubgroup (MulAut.conj y)) = ⊥ :=
    gLAPPrimeCoreOf_eq_bot_of_relIndex_eq_pow Nat.prime_five hSC hSnormal (k := 2)
      (by rw [hrel]; norm_num) hSbot
  rw [hCbot, Subgroup.card_bot]
  exact odd_one

theorem odd_card_gLAPPrimeCoreOf_fixSubgroup_fieldAut_of_orderOf_five
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * 2 + 1)) {σ : K ≃+* K} (hσ : orderOf σ = 5)
    (g : ↥(ReeTag.F4.reeGamma K 2)) :
    Odd (Nat.card (GLAPPrimeCoreOf 5 (fixSubgroup (MulAut.conj g *
      ReeTag.F4.reeGammaFieldAut K 2 σ * (MulAut.conj g)⁻¹)))) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  obtain ⟨b, hbp, hkcard, -⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK Nat.prime_five
      (by norm_num) σ hσ
  have hb0 : b = 0 := by
    have h1 : (2 * b + 1) * 5 = 5 := by simpa using hbp
    omega
  subst hb0
  have hk2 : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 := by simpa using hkcard
  obtain ⟨b', hkcard', hchar', ⟨eC⟩⟩ :=
    exists_fixSubgroup_fieldAut_equiv' (a := 2) hK Nat.prime_five (by norm_num) σ hσ
  haveI := hchar'
  have hb0' : b' = 0 := by
    have h1 : 2 ^ (2 * b' + 1) = 2 ^ 1 := by rw [← hkcard', hk2, pow_one]
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    omega
  subst hb0'
  have hcoreFix : CFSG.pPrimeCore 5
      ↥(ReeTag.F4.reeGamma (CFSG.LieType.Chevalley.fixSubfield σ) 0) = ⊥ :=
    pPrimeCore_five_reeGamma_zero hk2
  have hbotField : CFSG.pPrimeCore 5 ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K 2 σ)) = ⊥ :=
    pPrimeCore_eq_bot_of_mulEquiv 5 eC.symm hcoreFix
  have hbotα : CFSG.pPrimeCore 5 ↥(fixSubgroup (MulAut.conj g *
      ReeTag.F4.reeGammaFieldAut K 2 σ * (MulAut.conj g)⁻¹)) = ⊥ := by
    have h := pPrimeCore_eq_bot_of_mulEquiv 5
      (fixSubgroupCongrEquiv (MulAut.conj g) (ReeTag.F4.reeGammaFieldAut K 2 σ)) hbotField
    rwa [show MulAut.congr (MulAut.conj g : ↥(ReeTag.F4.reeGamma K 2) ≃* _)
      (ReeTag.F4.reeGammaFieldAut K 2 σ) =
        MulAut.conj g * ReeTag.F4.reeGammaFieldAut K 2 σ * (MulAut.conj g)⁻¹ from rfl] at h
  rw [gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr hbotα, Subgroup.card_bot]
  exact odd_one

theorem oddCoreFact_five_reeGamma_two {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    OddCoreFact 5 ↥(ReeTag.F4.reeGamma K 2) := by
  have hZ : Subgroup.center ↥(ReeTag.F4.reeGamma K 2) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial 2 K hK
  constructor
  ·
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_full_inner_field_automorphism_normal_form
        2 (by norm_num) K hK
    have hodd : Odd (Nat.card (Outer ↥(ReeTag.F4.reeGamma K 2))) := by
      rw [hcard]
      norm_num
    exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
      (CFSG.Quasithin.H13.OutTwoNilp.twoNilpotent_of_odd hodd)
  · intro α hα
    have hα5 : α ^ 5 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    have hα1 : α ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hα
      norm_num at hα
    rw [odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff hZ 5 α]
    change Odd (Nat.card (GLAPPrimeCoreOf 5 (fixSubgroup α)))
    rcases reeF4_inner_or_field (a := 2) (by norm_num) hK Nat.prime_five hα5 hα1 with
      ⟨y, rfl, hy5, hy1⟩ | ⟨σ, g, hσ, rfl⟩
    · have hy : orderOf y = 5 := orderOf_eq_prime hy5 hy1
      exact odd_card_gLAPPrimeCoreOf_fixSubgroup_conj_of_orderOf_five hK hy
    · exact odd_card_gLAPPrimeCoreOf_fixSubgroup_fieldAut_of_orderOf_five hK hσ g

end Certificates

theorem oddCoreFact_five_of_reeF4_two
    {S : Type} [Group S] [Finite S] (hv : (TauCeti.LieTypeIndex.reeF4 2).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 2, hv⟩).Group) :
    OddCoreFact 5 S := by
  obtain ⟨X, _, _, _, -, hX, -, ⟨eCat⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  exact (oddCoreFact_congr (p := 5) (e.trans eCat)).mpr (oddCoreFact_five_reeGamma_two hX)

end CFSG.LocalAnalysis.GLTheoremA.KD1912
