module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Pair

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbedding

namespace AGLPair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem false_of_four_le_pRank (hD1 : D1For G) (h : AGLPair p M H R) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h4 : 4 ≤ Open.pRank q (H ⊓ M)) : False := by
  have hH4 : 4 ≤ Open.pRank q H := h4.trans (pRank_mono q hq inf_le_left)
  have hβ : q ∈ GLBBetaFour G := by
    refine ⟨hq, hq2, prime_dvd_card_of_positive_rank q hq H (by omega), ?_⟩
    exact hH4.trans (le_csSup (twoLocalRank_bddAbove q hq) ⟨H, h.maxTwoLocal_H.1, rfl⟩)
  exact false_of_guestPrime h.glob.pre hβ (hD1 q hβ) h.maxTwoLocal_M h.maxTwoLocal_H h.not_le
    (by omega)

theorem pRank_inf_le_three (hD1 : D1For G) (h : AGLPair p M H R) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) : Open.pRank q (H ⊓ M) ≤ 3 := by
  by_contra hlt
  exact h.false_of_four_le_pRank hD1 hq hq2 (by omega)

theorem pRank_inf_le_two_of_mem_betaFour (hD1 : D1For G) (h : AGLPair p M H R) {q : ℕ}
    (hq : q ∈ GLBBetaFour G) : Open.pRank q (H ⊓ M) ≤ 2 := by
  by_contra hlt
  exact false_of_guestPrime h.glob.pre hq (hD1 q hq) h.maxTwoLocal_M h.maxTwoLocal_H h.not_le
    (by omega)

end AGLPair

end CFSG.AGLEmbeddingD2
