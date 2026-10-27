module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Structure
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot

import CFSG.RankThree.PartOne.CTP.StrongPQuotient
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C
  CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M Q H F : Subgroup G} {q : ℕ}

theorem Setting1417.kStar_normal (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) : (AGL81C.kStar q M H).Normal := by
  have h := CFSG.LocalAnalysis.AGL81TheoremCD.Section15.starImg_normal
    (p := q) (H := H) (A := AGL81C.kSub q M H) (s.kStructure h1).1
  simpa only [AGL81C.kStar, AGL81C.starImg] using h

theorem Setting1417.isStronglyPEmbedded_starImg (s : Setting1417 G M Q H F q) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded q (AGL81C.starImg q H (H ⊓ M)) := by
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  have hdvd : q ∣ Nat.card (H ⊓ M : Subgroup G) := by
    obtain ⟨E, hEQ, hEea, hEcard⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := q) (k := 2)
        (H := Q) s.two_le_pRank_Q
    have hqE : q ∣ Nat.card E := by
      rw [hEcard]
      exact ⟨q, by ring⟩
    exact hqE.trans (Subgroup.card_dvd_of_le (hEQ.trans (le_inf s.nine.Q_le_H s.Q_le_M)))
  have hNY : primeComplementCore (G := ↥H) q ≤ (H ⊓ M).subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxM : (x : G) ∈ CFSG.Open.relPPrimeCore q H := by
      rw [CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map
        s.qPrime H]
      exact Subgroup.mem_map_of_mem H.subtype hx
    exact ⟨x.2, s.nine.relPPrimeCore_le hxM⟩
  have hpN : ¬ q ∣ Nat.card (primeComplementCore (G := ↥H) q) :=
    (Nat.Prime.coprime_iff_not_dvd s.qPrime).mp (primeComplementCore_coprime (G := ↥H) q)
  have h := CFSG.RankThree.PartOne.IsStronglyPEmbedded.map_quotient
    (p := q) (Y := (H ⊓ M).subgroupOf H)
    (N := primeComplementCore (G := ↥H) q)
    (CFSG.RankThree.PartOne.IsStronglyPEmbedded.subgroupOf s.strongQ s.not_le hdvd) hNY hpN
  simpa only [AGL81C.starImg] using h

theorem Setting1417.two_le_pRank_top_star (s : Setting1417 G M Q H F q) :
    2 ≤ CFSG.Open.pRank q (⊤ : Subgroup (↥H ⧸ primeComplementCore (G := ↥H) q)) := by
  have hQ : Q ≤ H ⊓ M := le_inf s.nine.Q_le_H s.Q_le_M
  have h2 : 2 ≤ CFSG.Open.pRank q (H ⊓ M) :=
    s.two_le_pRank_Q.trans (CFSG.SectionRank.pRank_mono s.qPrime.one_lt hQ)
  calc 2 ≤ CFSG.Open.pRank q (H ⊓ M) := h2
    _ = CFSG.Open.pRank q (AGL81C.starImg q H M) := by
          rw [CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pRank_starImg_eq_pRank_inf s.qPrime M]
    _ ≤ CFSG.Open.pRank q (⊤ : Subgroup (AGL81C.StarGroup q H)) :=
          CFSG.SectionRank.pRank_mono s.qPrime.one_lt le_top

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
