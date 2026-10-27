module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFive
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Structure
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZKFactsL34
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenTwoOneHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineSixPairFiveDirect
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Cases

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open Subgroup

theorem IsA6Type.of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsA6Type A) : IsA6Type B := by
  obtain ⟨f⟩ := h
  exact ⟨(QuotientGroup.congr (Subgroup.center B) (Subgroup.center A) e.symm
    (Subgroup.map_center_eq e.symm)).trans f⟩

namespace NineSettingGen

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p k : ℕ}

theorem pRank_le_three_of_mem_H2Fam (h : NineSettingGen G M 3 Q H E k)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) :
    CFSG.Open.pRank 3 H ≤ 3 := by
  have hcore : H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H :=
    (mem_H2Fam_iff.mp hH2).2.2.2
  have hO : pCoreOf 2 H ≠ ⊥ := by
    intro hb
    refine h.not_le ?_
    have hle : H ≤ ⊥ := by
      refine fun x hx => hb ▸ hcore ⟨hx, ?_⟩
      rw [hb]
      simp [Subgroup.mem_centralizer_iff]
    exact hle.trans bot_le
  have hloc : IsTwoLocal (normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hO, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H, rfl⟩
  have hHN : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  exact (CFSG.SectionRank.pRank_mono (by norm_num) hHN).trans
    (h.setting.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num)
      (h.nineFiveGen h3).1 hloc)

theorem pRank_quotient_le_three_of_mem_H2Fam (h : NineSettingGen G M 3 Q H E k)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) :
    CFSG.pRank 3 ↥(⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  calc CFSG.pRank 3 ↥(⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H))
      = CFSG.pRank 3 (↥H ⧸ CFSG.pPrimeCore 3 ↥H) :=
        CFSG.pRank_congr_of_mulEquiv Subgroup.topEquiv 3
    _ = CFSG.pRank 3 ↥H :=
        CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd
          Nat.prime_three _ hN
    _ = CFSG.Open.pRank 3 H := CFSG.SectionRank.pRank_coe_eq_openPRank 3 H
    _ ≤ 3 := pRank_le_three_of_mem_H2Fam h hH2 h3

theorem openPRank_starGroup_le_three (h : NineSettingGen G M 3 Q H E k)
    (hH2 : H ∈ H2Fam M Q) (h3 : 3 ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StarGroup 3 H)) ≤ 3 :=
  (CFSG.SectionRank.pRank_coe_eq_openPRank 3 (⊤ : Subgroup (StarGroup 3 H))).symm.trans_le
    (pRank_quotient_le_three_of_mem_H2Fam h hH2 h3)

theorem starImg_not_le (h : NineSettingGen G M p Q H E k) {J : Subgroup G} (hJH : J ≤ H)
    (hJM : ¬ J ≤ M) : ¬ starImg p H J ≤ starImg p H M :=
  fun hle => hJM ((h.toCore.le_iff_starImg_le hJH).2 hle)

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem two_le_pRank_starImg_of_isL34Type {H J : Subgroup G} (hJ : IsPComponentIn 3 J H)
    (hL : IsL34Type (threeStar J)) : 2 ≤ CFSG.Open.pRank 3 (starImg 3 H J) := by
  obtain ⟨e⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hJ
  have hq : CFSG.IsQuasisimple ↥(starImg 3 H J) := (isComponent_starImg hJ).1
  have h2 := kFactThreeRankL34_holds ↥(starImg 3 H J) hq (IsL34Type.of_mulEquiv e hL)
  rwa [CFSG.pRank_congr_of_mulEquiv Subgroup.topEquiv 3,
    CFSG.SectionRank.pRank_coe_eq_openPRank 3 (starImg 3 H J)] at h2

theorem three_le_pRank_starImg_of_isA11Star {H J : Subgroup G} (hJ : IsPComponentIn 3 J H)
    (hA : IsA11Star J) : 3 ≤ CFSG.Open.pRank 3 (starImg 3 H J) := by
  obtain ⟨e⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hJ
  obtain ⟨f⟩ := hA
  exact CFSG.AGLEmbeddingD2.AltDegree.three_le_pRank_of_mulEquiv_alternating
    Nat.prime_three (by norm_num) (by norm_num : 3 * 3 ≤ 11) (e.symm.trans f)

theorem exists_noncentral_of_isComponent {X : Type} [Group X] [Finite X]
    (hK : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore 3 X = ⊥) {C : Subgroup X}
    (hC : CFSG.IsComponent C) : ∃ e ∈ C, orderOf e = 3 ∧ ∃ c ∈ C, e * c ≠ c * e :=
  kFactOmegaNotCentral_holds X hK C hC 3 Nat.prime_three (by norm_num)
    (CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card Nat.prime_three hO hC)

theorem pRank_add_one_le_of_ne {X : Type} [Group X] [Finite X] (hK : CFSG.Open.IsKGroup X)
    (hO : CFSG.pPrimeCore 3 X = ⊥) {L I : Subgroup X} (hL : CFSG.IsComponent L)
    (hI : CFSG.IsComponent I) (hLI : L ≠ I) :
    CFSG.Open.pRank 3 I + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section12.pRank_add_one_le_of_ne_prime hK
    Nat.prime_three (by norm_num) hO hL hI hLI

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
