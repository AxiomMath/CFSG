module

public import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedFamily

import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X81Conf
import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma22
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedComponentTools
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedConjugacy
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedTransport
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreActiveTwoComponent
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapLift
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Basic
import CFSG.Foundations.GilmanSolomonGrammar
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27QuotientIndex
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.CyclicBlocks.Family
import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
import CFSG.ClassicalGroups
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.GLS.Bg.Statements
import CFSG.GH74.GLS.Defs
import CFSG.GH74.Statements
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.LieType.Universal.Spin.Roots
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LieType.Universal.Unitary
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
import CFSG.LocalAnalysis.ComponentClassification.AS76bHypII
import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
import CFSG.LocalAnalysis.ComponentClassification.FooteLitBalanceCore
import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bL34Tools
import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Inst
import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Statement
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34
import CFSG.LocalAnalysis.ComponentClassification.Sol76Props
import CFSG.LocalAnalysis.OddStandard.Solomon75GH71Defs
import CFSG.LocalAnalysis.OddStandard.Solomon75Goldschmidt
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma34
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Center
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Struct
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOuterTools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_commute_of_even {a : G} (ha : orderOf a = 2) {Q : Subgroup G}
    (hQ : Even (Nat.card Q)) (haQ : a ∈ normalizer (Q : Set G)) :
    ∃ b ∈ Q, orderOf b = 2 ∧ a * b = b * a := by
  have ha2 : a * a = 1 := by
    rw [← pow_two, ← ha]
    exact pow_orderOf_eq_one a
  obtain ⟨b, hbQ, hb2, hba⟩ :=
    CFSG.ComponentClassification.AS76b.Lemma34.exists_involution_commute
      (X := Q) (u := a) ha2 haQ hQ
  exact ⟨b, hbQ, hb2, hba.symm⟩

theorem isComponent_map_conj {K : Subgroup G} (hK : IsComponent K) (g : G) :
    IsComponent (K.map (MulAut.conj g).toMonoidHom) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK

theorem isPComponent_subgroupOf_of_isComponent {K X : Subgroup G} (hK : IsComponent K)
    (hKX : K ≤ X) : IsPComponent 2 (K.subgroupOf X) :=
  CFSG.OddStandard.Solomon75.isPComponent_two_of_isQuasisimple_of_subnormal
    hK.1 hKX (hK.2.comap X.subtype)

theorem le_centralizer_of_isComponent_of_ne {K L : Subgroup G} (hK : IsComponent K)
    (hL : IsComponent L) (hne : K ≠ L) : K ≤ centralizer (L : Set G) := by
  have hcomm : ⁅L, K⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hL hK).resolve_left (Ne.symm hne)
  rw [Subgroup.commutator_comm] at hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem even_card_of_isComponent {K : Subgroup G} (hK : IsComponent K) :
    Even (Nat.card K) := by
  obtain ⟨b, hbK, hb2⟩ :=
    exists_involution_of_isTwoComponentIn (K := K) (X := ⊤)
      ⟨le_top, isPComponent_subgroupOf_of_isComponent hK le_top⟩
  have hb2' : orderOf (⟨b, hbK⟩ : K) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨b, hbK⟩ : K)]
    exact hb2
  have hdvd : orderOf (⟨b, hbK⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  rw [hb2'] at hdvd
  exact even_iff_two_dvd.mpr hdvd

theorem map_conj_map_conj_of_orderOf_eq_two {a : G} (ha : orderOf a = 2) (K : Subgroup G) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a).toMonoidHom = K := by
  rw [Subgroup.map_conj_map_conj]
  have ha2 : a * a = 1 := by
    rw [← pow_two, ← ha]
    exact pow_orderOf_eq_one a
  rw [ha2, map_one]
  change K.map (MonoidHom.id G) = K
  exact Subgroup.map_id K

theorem ncard_le_two_of_subset_pair {𝒦 : Set (Subgroup G)} {X Y : Subgroup G}
    (hsub : 𝒦 ⊆ {X, Y}) : 𝒦.ncard ≤ 2 ∧ (2 ≤ 𝒦.ncard → X ∈ 𝒦 ∧ Y ∈ 𝒦) := by
  have hle : 𝒦.ncard ≤ ({X, Y} : Set (Subgroup G)).ncard := Set.ncard_le_ncard hsub
  have hpair : ({X, Y} : Set (Subgroup G)).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le (a := X) (s := {Y})
  refine ⟨hle.trans hpair, fun h2 => ⟨?_, ?_⟩⟩
  · by_contra hX
    have hsubY : 𝒦 ⊆ {Y} := by
      intro K hK
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hsub hK) with rfl | h
      · exact absurd hK hX
      · exact h
    have h1 : 𝒦.ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard hsubY
    omega
  · by_contra hY
    have hsubX : 𝒦 ⊆ {X} := by
      intro K hK
      rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hsub hK) with h | rfl
      · exact h
      · exact absurd hK hY
    have h1 : 𝒦.ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard hsubX
    omega

theorem isComponent_map_of_isTwoComponentIn {K H : Subgroup G}
    (hK : FooteLit.IsTwoComponentIn K H) :
    IsComponent ((K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))) := by
  obtain ⟨L, hL, -, hmap, -⟩ := hK.2
  rw [hmap]
  exact hL

theorem map_conjugate_subgroupOf_eq {K H : Subgroup G} (hKH : K ≤ H) {a : ↥H}
    (ha : orderOf a = 2) :
    ((CFSG.conjugate K (a : G)).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) =
      ((K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))).map
        (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥H) a)).toMonoidHom := by
  have hπa : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥H) a) = 2 := by
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥H)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥H))
    exact UnbalancedLayer.orderOf_mk_eq_two (R := pPrimeCore 2 ↥H) hodd ha
  rw [← UnbalancedLayer.conjugate_subgroupOf_eq K H a,
    CFSG.QuasithinUnique.I32.map_conjugate, CFSG.GSGrammar.conjugate_eq_map_conj hπa]

theorem injOn_map_of_isTwoComponentIn (H : Subgroup G) :
    Set.InjOn (fun K : Subgroup G => (K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)))
      {K | FooteLit.IsTwoComponentIn K H} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro K hK L hL hmap
  have hsub : K.subgroupOf H = L.subgroupOf H :=
    UnbalancedLayer.pComponent_eq_of_map_eq hK.2 hL.2 hmap
  have h := congrArg (Subgroup.map H.subtype) hsub
  simpa only [Subgroup.map_subgroupOf_eq_of_le hK.1,
    Subgroup.map_subgroupOf_eq_of_le hL.1] using h

theorem even_card_map_quotient {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : Even (Nat.card Q)) :
    Even (Nat.card ((Q.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)))) := by
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  let K : Subgroup ↥H := (Q.subgroupOf H) ⊓ π.ker
  have hcard :
      Nat.card (Q.subgroupOf H) = Nat.card ((Q.subgroupOf H).map π) * Nat.card K :=
    CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker π (Q.subgroupOf H)
  have hcardQ : Nat.card (Q.subgroupOf H) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv
  have hker : π.ker = pPrimeCore 2 ↥H := QuotientGroup.ker_mk' _
  have hKodd : Odd (Nat.card K) := by
    have hdvd : Nat.card K ∣ Nat.card (pPrimeCore 2 ↥H) := by
      rw [← hker]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥H))).of_dvd_nat hdvd
  have hprod : Even (Nat.card ((Q.subgroupOf H).map π) * Nat.card K) := by
    rw [← hcard, hcardQ]
    exact hQ
  rw [even_iff_two_dvd] at hprod ⊢
  have hnot : ¬ 2 ∣ Nat.card K := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h)
  rcases (Nat.prime_two.dvd_mul.mp hprod) with h | h
  · exact h
  · exact absurd h hnot

theorem mem_normalizer_baseKernel {T : Type} [Group T] {𝓢 : Set (Subgroup G)}
    (hFam : IsomorphicFamily 𝓢 T) {H : Subgroup G} {g : G} (hg : g ∈ H) :
    g ∈ normalizer (baseKernel 𝓢 T H : Set G) := by
  have hbase : g ∈ normalizer (base H : Set G) := by
    have hconjH : CFSG.conjugate H g = H :=
      UnbalancedLayer.conjugate_eq_of_mem_normalizer (Subgroup.le_normalizer hg)
    have hbase_eq : CFSG.conjugate (base H) g = base H := by
      rw [base_conjugate, hconjH]
    exact UnbalancedLayer.mem_normalizer_of_conjugate_eq hbase_eq
  have hD : g ∈ normalizer (markedLayer 𝓢 T H : Set G) :=
    markedLayer_le_normalizer hFam H hg
  have hcore : g ∈ normalizer
      (UnbalancedLayer.coreActionKernel (markedLayer 𝓢 T H) : Set G) :=
    CFSG.ComponentClassification.GSThmB.X81.mem_normalizer_coreActionKernel hD
  have hker : g ∈ normalizer
      ((base H ⊓ UnbalancedLayer.coreActionKernel (markedLayer 𝓢 T H) : Subgroup G) : Set G) :=
    FooteLit.mem_normalizer_inf' hbase hcore
  simpa [baseKernel] using hker

theorem mk_mem_normalizer_map {H Q : Subgroup G} (hQH : Q ≤ H) {g : ↥H}
    (hg : (g : G) ∈ normalizer (Q : Set G)) :
    QuotientGroup.mk' (pPrimeCore 2 ↥H) g ∈
      normalizer (((Q.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :
        Subgroup (↥H ⧸ pPrimeCore 2 ↥H)) : Set (↥H ⧸ pPrimeCore 2 ↥H)) := by
  have hg' : g ∈ normalizer ((Q.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro x
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using hg (x : G)
  exact UnbalancedLayer.map_mem_normalizer (QuotientGroup.mk' (pPrimeCore 2 ↥H)) hg'

theorem map_baseKernel_le_centralizer {T : Type} [Group T] {𝓢 : Set (Subgroup G)}
    (hFam : IsomorphicFamily 𝓢 T) {H K : Subgroup G} (hK : K ∈ markedComponents 𝓢 T H) :
    ((baseKernel 𝓢 T H).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) ≤
      centralizer (((K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) :
        Subgroup (↥H ⧸ pPrimeCore 2 ↥H)) : Set (↥H ⧸ pPrimeCore 2 ↥H)) := by
  let D := markedLayer 𝓢 T H
  have hKle : K ≤ D := le_sSup hK
  have hKH : K ≤ H := hK.1.1
  have hDH : D ≤ H := markedLayer_le 𝓢 T H
  have hDnorm : H ≤ normalizer (D : Set G) := markedLayer_le_normalizer hFam H
  have hOleH : FooteLit.oddCoreIn D ≤ H := (map_subtype_le _).trans hDH
  have hOnorm : H ≤ normalizer (FooteLit.oddCoreIn D : Set G) :=
    fun h hh => FooteLit.mem_normalizer_oddCoreIn (hDnorm hh)
  have hODodd : Odd (Nat.card (FooteLit.oddCoreIn D)) := FooteLit.odd_card_oddCoreIn D
  have hOleOH : FooteLit.oddCoreIn D ≤ FooteLit.oddCoreIn H :=
    FooteLit.le_oddCoreIn hOleH hOnorm hODodd
  intro y hy
  obtain ⟨x, hxker, rfl⟩ := Subgroup.mem_map.mp hy
  have hxbase : (x : G) ∈ base H := (Subgroup.mem_subgroupOf.mp hxker).1
  have hxcore : (x : G) ∈ UnbalancedLayer.coreActionKernel D :=
    (Subgroup.mem_subgroupOf.mp hxker).2
  have hxact := (UnbalancedLayer.mem_coreActionKernel.mp hxcore).2
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨k, hkker, rfl⟩ := Subgroup.mem_map.mp hz
  have hk : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hkker
  have hkD : (k : G) ∈ D := hKle hk
  have hcommD : (k : G)⁻¹ * (x : G)⁻¹ * (k : G) * (x : G) ∈ FooteLit.oddCoreIn D :=
    hxact (k : G) hkD
  have hcommH : (k : G)⁻¹ * (x : G)⁻¹ * (k : G) * (x : G) ∈ FooteLit.oddCoreIn H :=
    hOleOH hcommD
  have hmem : (k⁻¹ * x⁻¹ * k * x : ↥H) ∈ pPrimeCore 2 ↥H := by
    obtain ⟨v, hv, hvval⟩ := Subgroup.mem_map.mp hcommH
    have hveq : v = k⁻¹ * x⁻¹ * k * x := by
      apply Subtype.ext
      calc
        (v : G) = (k : G)⁻¹ * (x : G)⁻¹ * (k : G) * (x : G) := hvval
        _ = ((k⁻¹ * x⁻¹ * k * x : ↥H) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rwa [← hveq]
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥H) (k⁻¹ * x⁻¹ * k * x) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hmem
  have h2 : (QuotientGroup.mk' (pPrimeCore 2 ↥H) k)⁻¹ *
      (QuotientGroup.mk' (pPrimeCore 2 ↥H) x)⁻¹ *
      QuotientGroup.mk' (pPrimeCore 2 ↥H) k *
      QuotientGroup.mk' (pPrimeCore 2 ↥H) x = 1 := by
    simpa only [map_mul, map_inv] using h1
  have h3 : (QuotientGroup.mk' (pPrimeCore 2 ↥H) k)⁻¹ *
      (QuotientGroup.mk' (pPrimeCore 2 ↥H) x)⁻¹ =
      (QuotientGroup.mk' (pPrimeCore 2 ↥H) x)⁻¹ *
      (QuotientGroup.mk' (pPrimeCore 2 ↥H) k)⁻¹ := by
    have h := congrArg
      (fun t => t * (QuotientGroup.mk' (pPrimeCore 2 ↥H) k *
        QuotientGroup.mk' (pPrimeCore 2 ↥H) x)⁻¹) h2
    simpa [mul_assoc, mul_inv_rev] using h
  have h4 : QuotientGroup.mk' (pPrimeCore 2 ↥H) x *
      QuotientGroup.mk' (pPrimeCore 2 ↥H) k =
      QuotientGroup.mk' (pPrimeCore 2 ↥H) k *
      QuotientGroup.mk' (pPrimeCore 2 ↥H) x := by
    simpa only [mul_inv_rev, inv_inv] using congrArg Inv.inv h3
  exact h4.symm

theorem orderOf_mk_eq_two {H : Subgroup G} {a : ↥H} (ha : orderOf a = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥H) a) = 2 := by
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥H))
  exact UnbalancedLayer.orderOf_mk_eq_two (R := pPrimeCore 2 ↥H) hodd ha

theorem map_eq_map_fixedShadowAt {T : Type} [Group T] {𝓢 : Set (Subgroup G)}
    (hFam : IsomorphicFamily 𝓢 T) {H M : Subgroup G} (hM : Marked 𝓢 T M) (hMH : M ≤ H)
    {a : ↥H} (ha : orderOf a = 2) (haM : (a : G) ∈ UnbalancedLayer.coreActionKernel M)
    (hA : IsComponent (((fixedShadowAt M a).subgroupOf H).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥H)))) :
    (M.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) =
      ((fixedShadowAt M a).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) := by
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  let U : Subgroup G := zpowers (a : G)
  have haG : orderOf (a : G) = 2 := (Subgroup.orderOf_coe a).trans ha
  have hU : IsPGroup 2 U :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, haG, pow_one])
  have haU : (a : G) ∈ U := Subgroup.mem_zpowers _
  have hUK : U ≤ UnbalancedLayer.coreActionKernel M := Subgroup.zpowers_le.mpr haM
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) := hM.quotient_quasisimple hFam
  obtain ⟨hcover, -, -⟩ := fixedShadow_cover_quotient hMq hU hUK
  rw [fixedShadow_zpowers] at hcover
  let Ma : Subgroup G := fixedShadowAt M (a : G)
  let O : Subgroup G := FooteLit.oddCoreIn M
  have hMaH : Ma ≤ H := (fixedShadowAt_le M (a : G)).trans hMH
  have hOH : O ≤ H := (map_subtype_le _).trans hMH
  have hsub_eq : M.subgroupOf H = Ma.subgroupOf H ⊔ O.subgroupOf H := by
    rw [← hcover, Subgroup.subgroupOf_sup hMaH hOH]
  let X : Subgroup (↥H ⧸ pPrimeCore 2 ↥H) := (Ma.subgroupOf H).map π
  let V : Subgroup (↥H ⧸ pPrimeCore 2 ↥H) := (M.subgroupOf H).map π
  let R : Subgroup (↥H ⧸ pPrimeCore 2 ↥H) := (O.subgroupOf H).map π
  have hVeq : V = X ⊔ R := by
    change (M.subgroupOf H).map π = (Ma.subgroupOf H).map π ⊔ (O.subgroupOf H).map π
    rw [hsub_eq, Subgroup.map_sup]
  have hXV : X ≤ V := by rw [hVeq]; exact le_sup_left
  have hRV : R ≤ V := by rw [hVeq]; exact le_sup_right
  have hVperf : Group.IsPerfect ↥V := by
    haveI : Group.IsPerfect ↥M := hM.1
    have hperf : Group.IsPerfect ↥(M.subgroupOf H) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hMH).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hMH).symm.surjective
    exact Group.IsPerfect.ofSurjective (f := π.subgroupMap (M.subgroupOf H))
      (π.subgroupMap_surjective (M.subgroupOf H))
  have hRodd : Odd (Nat.card ↥R) := by
    have hOodd : Odd (Nat.card O) := FooteLit.odd_card_oddCoreIn M
    have hdvd : Nat.card R ∣ Nat.card O := by
      calc Nat.card R ∣ Nat.card (O.subgroupOf H) :=
            Subgroup.card_map_dvd (O.subgroupOf H) π
        _ = Nat.card O := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv
    exact hOodd.of_dvd_nat hdvd
  have hVle : V ≤ FooteLit.conjClosure X V ⊔ R := by
    rw [hVeq]
    refine sup_le ?_ ?_
    · exact (FooteLit.le_conjClosure X (X ⊔ R)).trans
        (le_sup_left : FooteLit.conjClosure X (X ⊔ R) ≤
          FooteLit.conjClosure X (X ⊔ R) ⊔ R)
    · exact le_sup_right
  have hVX : V = X :=
    eq_of_perfect_le_conjClosure_sup_odd hA hXV hVperf hRV hRodd hVle
  exact hVX

end CFSG.ComponentClassification.FooteMarked
