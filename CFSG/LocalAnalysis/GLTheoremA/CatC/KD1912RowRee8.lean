module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4Gen
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Dickson.SuzukiReeB
open CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open CFSG.RankThree.LargeReeOrder
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Certificates


theorem pPrimeCore_three_reeGamma_zero {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) :
    CFSG.pPrimeCore 3 (ReeTag.F4.reeGamma k 0) = ⊥ := by
  obtain ⟨hsimple, -, ⟨hcat⟩⟩ := commutator_reeGamma_F4_zero_data hk
  let C := ReeTag.F4.reeGamma k 0
  let T : Subgroup C := commutator C
  have hTnorm : T.Normal := inferInstance
  haveI : IsSimpleGroup ↥T := hsimple
  have hZ : Subgroup.center C = ⊥ := ReeTag.large_Ree_fixed_group_center_trivial 0 k hk
  have hCcard : Nat.card C = 35942400 := by
    rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion 0 k hk).1]
    norm_num
  have hTcard : Nat.card ↥T = 17971200 := rf4_card_tits ⟨hcat⟩
  have hindex : T.index = 2 := by
    have h := Subgroup.card_mul_index T
    rw [hTcard, hCcard] at h
    omega
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro N hN hcop
  haveI := hN
  haveI := hTnorm
  have hMn : (N ⊓ T).Normal := inferInstance
  haveI := hMn
  have hMTn : ((N ⊓ T).subgroupOf T).Normal := inferInstance
  have hNT : N ⊓ T = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ T).subgroupOf T) with h | h
    · rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : N ⊓ T ≤ T), h, Subgroup.map_bot]
    · exfalso
      have hTN : T ≤ N := ((Subgroup.subgroupOf_eq_top.1 h).trans inf_le_left)
      have h3T : 3 ∣ Nat.card ↥T := by rw [hTcard]; norm_num
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
        (h3T.trans (Subgroup.card_dvd_of_le hTN))
  have hinj : Function.Injective
      (fun n : ↥N => (QuotientGroup.mk' T (n : C) : C ⧸ T)) := by
    intro a b hab
    apply Subtype.ext
    have h1 : QuotientGroup.mk' T ((a : C)⁻¹ * (b : C)) = 1 := by
      rw [map_mul, map_inv, show QuotientGroup.mk' T (a : C) = QuotientGroup.mk' T (b : C) from hab,
        inv_mul_cancel]
    have h2 : (a : C)⁻¹ * (b : C) ∈ N ⊓ T :=
      ⟨N.mul_mem (N.inv_mem a.2) b.2, (QuotientGroup.eq_one_iff _).1 h1⟩
    rw [hNT, Subgroup.mem_bot] at h2
    exact eq_of_inv_mul_eq_one h2
  have hle : Nat.card ↥N ≤ Nat.card (C ⧸ T) :=
    Nat.card_le_card_of_injective _ hinj
  have hquot : Nat.card (C ⧸ T) = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  have hNle : Nat.card ↥N ≤ 2 := by rw [hquot] at hle; exact hle
  have hNcard : Nat.card ↥N = 1 := by
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    rcases (show Nat.card ↥N = 1 ∨ Nat.card ↥N = 2 by omega) with h1 | h2
    · exact h1
    · exfalso
      have hle_center : N ≤ Subgroup.center C :=
        CFSG.ABGLocalTools.le_center_of_normal_of_card_eq_two hN h2
      rw [hZ] at hle_center
      have hbot : N = ⊥ := le_bot_iff.1 hle_center
      rw [hbot] at h2
      simp at h2
  exact Subgroup.card_eq_one.1 hNcard

theorem oddCoreFact_three_reeGamma_one {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * 1 + 1)) :
    OddCoreFact 3 (ReeTag.F4.reeGamma K 1) := by
  have hZ : Subgroup.center (ReeTag.F4.reeGamma K 1) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial 1 K hK
  constructor
  ·
    have hodd : Odd (Nat.card (Outer (ReeTag.F4.reeGamma K 1))) := by
      obtain ⟨-, -, -, -, hcard, -⟩ :=
        large_Ree_full_inner_field_automorphism_normal_form 1 (by norm_num) K hK
      rw [hcard]
      norm_num
    exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
      (CFSG.Quasithin.H13.OutTwoNilp.twoNilpotent_of_odd hodd)
  · intro α hα
    have hα3 : α ^ 3 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    have hα1 : α ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hα
      norm_num at hα
    rw [odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff hZ 3 α]
    change Odd (Nat.card (GLAPPrimeCoreOf 3 (fixSubgroup α)))
    rcases reeF4_inner_or_field (a := 1) (by norm_num) hK Nat.prime_three hα3 hα1 with
      ⟨y, rfl, hy3, hy1⟩ | ⟨σ, g, hσ, rfl⟩
    ·
      rw [fixSubgroup_conj]
      obtain ⟨eSU⟩ := centralizer_mulEquiv_unitarySU 1 K hK y (orderOf_eq_prime hy3 hy1)
      have hF : Nat.card (GaloisField 2 (2 * (2 * 1 + 1))) = (2 ^ 3) ^ 2 := by
        rw [GaloisField.card 2 _ (by norm_num)]
        norm_num
      have hqSU : CFSG.Open.IsQuasisimple
          (CFSG.Open.StatedSU 3 (2 ^ 3) (GaloisField 2 (2 * (2 * 1 + 1)))) :=
        CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
          (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
            (F := GaloisField 2 (2 * (2 * 1 + 1))) (f := 3) hF (by norm_num)).1
      have hq : CFSG.Open.IsQuasisimple
          ↥(Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K 1))) :=
        CFSG.Open.IsQuasisimple.of_mulEquiv eSU hqSU
      have hZcard : Nat.card (Subgroup.center
          ↥(Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K 1)))) = 3 := by
        rw [Nat.card_congr (Subgroup.centerCongr eSU).toEquiv]
        exact CFSG.Open.StatedCenterThree.card_center_statedSU_three (q := 8) hF (by norm_num)
      have hO : CFSG.pPrimeCore 3
          ↥(Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K 1))) = ⊥ :=
        CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPPrimeCore_eq_bot_of_quasisimple
          hq hZcard
      rw [gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr hO, Subgroup.card_bot]
      exact odd_one
    ·
      obtain ⟨b, hbp, hkcard, -⟩ :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK Nat.prime_three
          (by norm_num) σ hσ
      have hb0 : b = 0 := by
        have h1 : (2 * b + 1) * 3 = 3 := by simpa using hbp
        omega
      subst hb0
      have hk2 : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 := by
        simpa using hkcard
      obtain ⟨b', hkcard', hchar', ⟨eC⟩⟩ :=
        exists_fixSubgroup_fieldAut_equiv' (a := 1) hK Nat.prime_three (by norm_num) σ hσ
      haveI := hchar'
      have hb0' : b' = 0 := by
        have h1 : 2 ^ (2 * b' + 1) = 2 ^ 1 := by
          rw [← hkcard', hk2]
          norm_num
        have h2 := Nat.pow_right_injective (le_refl 2) h1
        omega
      subst hb0'
      have hcoreFix : CFSG.pPrimeCore 3
          ↥(ReeTag.F4.reeGamma (CFSG.LieType.Chevalley.fixSubfield σ) 0) = ⊥ :=
        pPrimeCore_three_reeGamma_zero hk2
      have hbotField : CFSG.pPrimeCore 3
          ↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K 1 σ)) = ⊥ :=
        pPrimeCore_eq_bot_of_mulEquiv 3 eC.symm hcoreFix
      have hbotα : CFSG.pPrimeCore 3
          ↥(fixSubgroup (MulAut.conj g * ReeTag.F4.reeGammaFieldAut K 1 σ *
            (MulAut.conj g)⁻¹)) = ⊥ := by
        have h := pPrimeCore_eq_bot_of_mulEquiv 3
          (fixSubgroupCongrEquiv (MulAut.conj g : ReeTag.F4.reeGamma K 1 ≃*
            ReeTag.F4.reeGamma K 1) (ReeTag.F4.reeGammaFieldAut K 1 σ)) hbotField
        rwa [show MulAut.congr (MulAut.conj g : ReeTag.F4.reeGamma K 1 ≃*
            ReeTag.F4.reeGamma K 1) (ReeTag.F4.reeGammaFieldAut K 1 σ) =
          MulAut.conj g * ReeTag.F4.reeGammaFieldAut K 1 σ * (MulAut.conj g)⁻¹ from rfl] at h
      rw [gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr hbotα, Subgroup.card_bot]
      exact odd_one

end Certificates

theorem oddCoreFact_three_of_reeF4_one
    {S : Type} [Group S] [Finite S] (hv : (TauCeti.LieTypeIndex.reeF4 1).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 1, hv⟩).Group) :
    OddCoreFact 3 S := by
  obtain ⟨X, _, _, _, -, hX, -, ⟨eCat⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  exact (oddCoreFact_congr (p := 3) (e.trans eCat)).mpr
    (oddCoreFact_three_reeGamma_one hX)

end CFSG.LocalAnalysis.GLTheoremA.KD1912
