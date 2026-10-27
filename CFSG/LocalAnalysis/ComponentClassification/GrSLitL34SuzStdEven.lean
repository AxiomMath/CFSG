module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdEvenCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.LocalNoSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Layer0

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

private theorem standardComponentOddCore_eq_bot_of_oddIn_eq_bot
    {G : Type} [Group G] [Finite G] {H : Subgroup G} (h : oddIn H = ⊥) :
    CFSG.Open.standardComponentOddCore H = ⊥ := by
  have hmap : (CFSG.Open.standardComponentOddCore H).map H.subtype = ⊥ := by
    rw [show CFSG.Open.standardComponentOddCore H = Assembly.oddCore H from rfl,
      CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    exact h
  exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.Open.standardComponentOddCore H)
    H.subtype_injective).mp hmap

theorem relIndex_dvd_two_of_outer_index_dvd_two {G : Type} [Group G] [Finite G]
    {A M : Subgroup G} (hperf : commutator A = ⊤) (hMN : M ≤ normalizer (A : Set G))
    (hCM : centralizer (A : Set G) ≤ A)
    (hout : (MulAut.conj : (A ⧸ center A) →* MulAut (A ⧸ center A)).range.index ∣ 2) :
    A.relIndex M ∣ 2 := by
  have hsub : (A ⊔ centralizer (A : Set G)).subgroupOf M =
      (MulAut.conj : (A ⧸ center A) →* MulAut (A ⧸ center A)).range.comap
        ((CFSG.EvenSporadicStandard.normalizerAction A).comp (Subgroup.inclusion hMN)) := by
    ext g
    exact (CFSG.EvenSporadicStandard.normalizerAction_mem_range_conj_iff hperf
      (Subgroup.inclusion hMN g)).symm
  have : ((MulAut.conj : (A ⧸ center A) →* MulAut (A ⧸ center A)).range).Normal :=
    CFSG.EvenSporadicStandard.normal_range_conj _
  have hdvd : (A ⊔ centralizer (A : Set G)).relIndex M ∣
      (MulAut.conj : (A ⧸ center A) →* MulAut (A ⧸ center A)).range.index := by
    rw [Subgroup.relIndex, hsub, Subgroup.index_comap]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  rw [sup_eq_left.2 hCM] at hdvd
  exact hdvd.trans hout

private theorem exists_center_involution_with_normalizers {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hA : IsStandardSubgroup A) (hEven : Even (Nat.card (center ↥A))) :
    ∃ t : G, t ∈ (center ↥A).map A.subtype ∧ orderOf t = 2 ∧
      t ∈ centralizer (A : Set G) ∧ t ∈ A ∧
      centralizer ({t} : Set G) ≤ normalizer (A : Set G) ∧
      centralizer ({t} : Set G) ≤ normalizer (centralizer (A : Set G) : Set G) := by
  obtain ⟨t₀, ht₀, ht₀order⟩ :=
    CFSG.StandardSubgroupAPI.exists_mem_orderOf_eq_two_of_even
      (G := ↥A) (Q := center ↥A) hEven
  let t : G := A.subtype t₀
  have ht2 : orderOf t = 2 := by
    change orderOf ((t₀ : ↥A) : G) = 2
    rw [Subgroup.orderOf_coe, ht₀order]
  have htZ : t ∈ (center ↥A).map A.subtype := ⟨t₀, ht₀, rfl⟩
  have hstd : CFSG.Open.standardComponentIsStandard A := hA.standardComponentIsStandard
  have htCA : t ∈ A ⊓ centralizer (A : Set G) := by
    rw [← CFSG.EvenSporadicStandard.map_center_eq_inf_centralizer]
    exact htZ
  refine ⟨t, htZ, ht2, htCA.2, htCA.1, ?_, ?_⟩
  · intro g hg
    exact hstd.mem_normalizer_of_commute htCA.2 ht2 (mem_centralizer_singleton_iff.1 hg)
  · intro g hg
    exact hstd.mem_normalizer_centralizer_of_commute htCA.2 ht2
      (mem_centralizer_singleton_iff.1 hg)

private theorem centralizer_eq_zpowers_of_standardComponentOddCore_eq_bot {G : Type}
    [Group G] [Finite G] {A : Subgroup G} {t : G}
    (htC : t ∈ centralizer (A : Set G)) (ht2 : orderOf t = 2)
    (hN : centralizer ({t} : Set G) ≤ normalizer (centralizer (A : Set G) : Set G))
    (hcore : CFSG.Open.standardComponentOddCore (centralizer ({t} : Set G)) = ⊥)
    (hSylow : ∀ S : Sylow 2 ↥(centralizer (A : Set G)), Nat.card S = 2)
    (hle : centralizer (A : Set G) ≤ centralizer ({t} : Set G)) :
    centralizer (A : Set G) = zpowers t := by
  have h := CFSG.EvenSporadicStandard.inf_centralizer_singleton_eq_zpowers
    (C := centralizer (A : Set G)) htC ht2 hN hcore hSylow
  rwa [inf_eq_left.2 hle] at h

private theorem map_center_eq_zpowers_of_centralizer_eq_zpowers {G : Type} [Group G]
    {A : Subgroup G} {t : G} (hCGA : centralizer (A : Set G) = zpowers t) (htA : t ∈ A) :
    (center ↥A).map A.subtype = zpowers t := by
  rw [CFSG.EvenSporadicStandard.map_center_eq_inf_centralizer, hCGA]
  exact inf_eq_right.2 (zpowers_le.2 htA)

private theorem card_center_eq_two_of_even_of_map_center_eq_zpowers {G : Type} [Group G]
    [Finite G] {A : Subgroup G} {t : G} (hZeq : (center ↥A).map A.subtype = zpowers t)
    (ht2 : orderOf t = 2) (hEven : Even (Nat.card (center ↥A))) :
    Nat.card (center ↥A) = 2 := by
  have hdvd : Nat.card (center ↥A) ∣ 2 := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, hZeq, Nat.card_zpowers, ht2]
  have hle : Nat.card (center ↥A) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := even_iff_two_dvd.1 hEven
  have hpos : 0 < Nat.card (center ↥A) := Nat.card_pos
  omega

private theorem twoSuzSetup_of_center_eq_zpowers {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {t : G} (ht2 : orderOf t = 2)
    (hZeq : (center ↥A).map A.subtype = zpowers t) (hZcard : Nat.card (center ↥A) = 2)
    (hperf : commutator A = ⊤)
    (hSuz : Blueprint.NativeSporadic.IsSporadic (↥A ⧸ center ↥A) .Suz)
    (hle : A ≤ centralizer ({t} : Set G))
    (hN : centralizer ({t} : Set G) ≤ normalizer (A : Set G))
    (hrel : A.relIndex (centralizer ({t} : Set G)) ∣ 2) :
    CFSG.EvenSporadicStandard.TwoSuz.Setup G A t :=
  ⟨ht2, hZeq, hZcard, hperf, hSuz, hle, hN, hrel⟩

theorem l34SuzEvenStandardExclusion_of_inputs
    (hAS : RankTwoSporadic.SporadicCaseOdd .Suz)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25) (hS : SchreierFor Blueprint.Catalog)
    (hC4 : SuzONanNotProperFixedCatalog) (hSV : L34SuzSignalizerVanishing) :
    L34SuzEvenStandardExclusion := by
  intro G _ _ hbase A hA hSuz hEven
  have : IsSimpleGroup G := hbase.1
  have hnonab : ∃ g h : G, g * h ≠ h * g := hbase.2.1
  have hK : Assembly.KProper Blueprint.Catalog G := hbase.2.2.1
  have hU : ¬ OutcomeLocal.UOutcome G := hbase.2.2.2.2.1
  obtain ⟨t, htZ, ht2, htC, htA, hN_A, hN_core⟩ :=
    exists_center_involution_with_normalizers hA hEven
  have hSylow : ∀ S : Sylow 2 ↥(centralizer (A : Set G)), Nat.card S = 2 := fun S =>
    card_sylow_centralizer_eq_two_of_suz hAS hCIT h25 hnonab hK hU hA hSuz S
  have hrank : pRank 2 ↥(centralizer (A : Set G)) ≤ 1 :=
    CFSG.ComponentClassification.UnbalancedLayer.pRank_two_le_one_of_card_sylow_le
      (fun S => le_of_eq (hSylow S))
  have hD : oddIn (centralizer ({t} : Set G)) = ⊥ :=
    oddIn_centralizer_eq_bot_of_suz_even hS hC4 hSV hbase hA hSuz hrank ht2 htZ
  have hcore : CFSG.Open.standardComponentOddCore (centralizer ({t} : Set G)) = ⊥ :=
    standardComponentOddCore_eq_bot_of_oddIn_eq_bot hD
  have hle_CGA_Ct : centralizer (A : Set G) ≤ centralizer ({t} : Set G) := by
    intro c hc
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hc t htA).symm
  have hCGA_eq : centralizer (A : Set G) = zpowers t :=
    centralizer_eq_zpowers_of_standardComponentOddCore_eq_bot htC ht2 hN_core hcore hSylow
      hle_CGA_Ct
  have hCM : centralizer (A : Set G) ≤ A := by
    rw [hCGA_eq]
    exact zpowers_le.2 htA
  have hZeq : (center ↥A).map A.subtype = zpowers t :=
    map_center_eq_zpowers_of_centralizer_eq_zpowers hCGA_eq htA
  have hZcard : Nat.card (center ↥A) = 2 :=
    card_center_eq_two_of_even_of_map_center_eq_zpowers hZeq ht2 hEven
  have hle_cent : A ≤ centralizer ({t} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC a ha)
  have hperf : commutator A = ⊤ := hA.standardComponentIsStandard.1.1
  have hout : (MulAut.conj : (A ⧸ center A) →* MulAut (A ⧸ center A)).range.index ∣ 2 :=
    CFSG.EvenSporadicStandard.TwoSuz.index_dvd_two_of_isSporadic_suz hSuz
  have hrel : A.relIndex (centralizer ({t} : Set G)) ∣ 2 :=
    relIndex_dvd_two_of_outer_index_dvd_two hperf hN_A hCM hout
  have hset : CFSG.EvenSporadicStandard.TwoSuz.Setup G A t :=
    twoSuzSetup_of_center_eq_zpowers ht2 hZeq hZcard hperf hSuz hle_cent hN_A hrel
  exact CFSG.EvenSporadicStandard.TwoSuz.false_of_setup_of_centralizer_eq_zpowers
    hnonab hset hCGA_eq

end CFSG.ComponentClassification.GrSLit.L34Sec5S
