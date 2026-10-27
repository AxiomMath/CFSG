module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Basic
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

private theorem isPCompIn_two_of_isComponentIn_of_even {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (hK : Omega.IsComponentIn K H) (hev : 2 ∣ Nat.card ↥K) :
    GH74.GLS.IsPCompIn 2 H K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hK.1, CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hK.2 ?_⟩
  intro hle
  have h1 : Nat.card ↥(K.subgroupOf H) ∣ Nat.card ↥(CFSG.pPrimeCore 2 ↥H) :=
    Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv
  rw [h2] at h1
  have hcop : Nat.Coprime 2 (Nat.card ↥K) :=
    Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card
  have h1K := Nat.Coprime.eq_one_of_dvd hcop hev
  omega

theorem isILo_of_residual (hR : ResidualTwoRank) {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {y : G} (hy : orderOf y = 2) {K : Subgroup G}
    (hK : Omega.IsComponentIn K (centralizer ({y} : Set G))) (hres : IsResidualA2 ↥K) :
    GH74.GLS.IsILo 2 y K ∧ 3 ≤ CFSG.pRank 2 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCbal : CFSG.oddCore (centralizer ({y} : Set G)) = ⊥ := hbal y hy
  have hZ : IsPGroup 2 ↥(center ↥K) := isPGroup_two_center_of_isComponentIn hCbal hK
  have hQuasi : IsQuasisimple ↥K :=
    CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK.1).symm hK.2.1
  obtain ⟨hrank2, hrank3⟩ := hR ↥K hQuasi hZ hres
  obtain ⟨A, -, hAel, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup ↥K)
  have hAcard' : Nat.card A = 2 ^ CFSG.pRank 2 ↥K := by
    rw [hAcard, ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥K]
  have hAel' : IsElementaryAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).2 hAel
  have hKev : 2 ∣ Nat.card ↥K := by
    have hm1 : 1 ≤ CFSG.pRank 2 ↥K := by omega
    have hdvd : 2 ∣ Nat.card A := by
      rw [hAcard']
      exact ⟨2 ^ (CFSG.pRank 2 ↥K - 1), by
        rw [← pow_succ', Nat.sub_add_cancel hm1]⟩
    exact hdvd.trans (Subgroup.card_subgroup_dvd_card A)
  have hisPComp : GH74.GLS.IsPCompIn 2 (centralizer ({y} : Set G)) K :=
    isPCompIn_two_of_isComponentIn_of_even hK hKev
  have h3C : 3 ≤ CFSG.pRank 2 ↥(centralizer ({y} : Set G)) := by
    by_cases hyK : y ∈ K
    ·
      have hyc : (⟨y, hyK⟩ : ↥K) ∈ center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp (hK.1 g.2) y (by simp)).symm
      have hne : center ↥K ≠ ⊥ := by
        intro hbot
        have hyb : (⟨y, hyK⟩ : ↥K) ∈ (⊥ : Subgroup ↥K) := by rw [← hbot]; exact hyc
        have hy1 : y = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hyb)
        rw [hy1, orderOf_one] at hy
        norm_num at hy
      exact (hrank3 hne).trans
        (CFSG.RankThree.PartOne.OddCore37.pRank_le_of_le Nat.prime_two hK.1)
    ·
      let E : Subgroup G := A.map K.subtype
      have hE_le_K : E ≤ K := Subgroup.map_subtype_le A
      have hE_el : IsElementaryAbelian 2 E := by
        haveI := hAel'
        dsimp only [E]
        exact IsElementaryAbelian.map_subtype
      have hE_card : Nat.card E = 2 ^ CFSG.pRank 2 ↥K := by
        dsimp only [E]
        rw [Subgroup.card_map_of_injective K.subtype_injective, hAcard']
      have hyE : y ∉ E := fun h => hyK (hE_le_K h)
      have hy2 : y ^ 2 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
      have hcomm : ∀ e ∈ E, e * y = y * e := by
        intro e he
        exact (Subgroup.mem_centralizer_iff.mp (hK.1 (hE_le_K he)) y (by simp)).symm
      have hcard_sup : Nat.card ↥(E ⊔ zpowers y) = 2 ^ (CFSG.pRank 2 ↥K + 1) := by
        rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers (p := 2) Nat.prime_two E hy2 hyE
          hcomm, hE_card, pow_succ]
      have hzy_el : IsElementaryAbelian 2 (zpowers y) :=
        IsElementaryAbelian.zpowers_of_pow_eq_one hy2
      have hsup_el : IsElementaryAbelian 2 ↥(E ⊔ zpowers y) := by
        haveI := hE_el
        haveI := hzy_el
        refine IsElementaryAbelian.sup_of_le_centralizer (p := 2) ?_
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr hcomm
      have hle : E ⊔ zpowers y ≤ centralizer ({y} : Set G) := by
        refine sup_le (hE_le_K.trans hK.1) ?_
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_iff.mpr (fun b hb => by
          rw [Set.mem_singleton_iff.mp hb])
      have hcard3 : 2 ^ 3 ≤ Nat.card ↥(E ⊔ zpowers y) := by
        rw [hcard_sup]
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 (by omega)
      have hle_rank := CFSG.RankThree.PartOne.Planes.le_pRank_of_le_card Nat.prime_two hle
        hsup_el (k := 3) hcard3
      rwa [CFSG.RankThree.PartOne.assembly_pRank_eq Nat.prime_two
        (centralizer ({y} : Set G))] at hle_rank
  refine ⟨⟨hy, ?_, hisPComp⟩, ?_⟩
  · simpa [GH74.GLS.oBound] using h3C
  · have h3top : 3 ≤ CFSG.pRank 2 ↥(⊤ : Subgroup G) :=
      h3C.trans (CFSG.RankThree.PartOne.OddCore37.pRank_le_of_le Nat.prime_two le_top)
    rwa [CFSG.RankThree.PartTwo.pRank_congr_mulEquiv (p := 2) one_lt_two
      (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G)] at h3top

end CFSG.OddStandard.SmallF3.HypA2
