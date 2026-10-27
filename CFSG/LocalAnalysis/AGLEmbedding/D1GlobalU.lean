module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.Helpers

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem sigmaA_eq_betaFour_of_nonempty (h : (GLBBetaFour G).Nonempty) :
    rankThreeSigmaA G = GLBBetaFour G := by
  unfold rankThreeSigmaA
  dsimp only
  split_ifs with h1
  · rfl
  all_goals exact absurd h h1

theorem mem_sigmaA_of_mem_betaFour {q : ℕ} (hq : q ∈ GLBBetaFour G) : q ∈ rankThreeSigmaA G := by
  rw [sigmaA_eq_betaFour_of_nonempty ⟨q, hq⟩]
  exact hq

theorem four_le_evenRank_of_mem_betaFour {q : ℕ} (hq : q ∈ GLBBetaFour G) : 4 ≤ evenRank G :=
  hq.2.2.2.trans
    (CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank q hq.1 hq.2.1)

theorem betaFour_nonempty_of_four_le_evenRank (h : 4 ≤ evenRank G) : (GLBBetaFour G).Nonempty := by
  obtain ⟨q, L, hq, hq2, hL, hr⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.evenRank_attained (G := G) (by omega)
  refine ⟨q, hq, hq2, ?_, ?_⟩
  · exact CFSG.RankThreeCoreUniqueness.Helpers.prime_dvd_card_of_pRank_pos q L (by omega)
  · have hle : pRank q L ≤ GLBTwoLocalRank q G :=
      le_csSup ⟨Nat.card G, by
        rintro k ⟨H, -, rfl⟩
        exact CFSG.RankThreeCoreUniqueness.Helpers.pRank_le_card q hq.one_lt H⟩ ⟨L, hL, rfl⟩
    omega

theorem sigmaA_eq_betaFour (h : 4 ≤ evenRank G) : rankThreeSigmaA G = GLBBetaFour G :=
  sigmaA_eq_betaFour_of_nonempty (betaFour_nonempty_of_four_le_evenRank h)

theorem mem_betaFour_of_mem_sigmaA (h : 4 ≤ evenRank G) {q : ℕ} (hq : q ∈ rankThreeSigmaA G) :
    q ∈ GLBBetaFour G :=
  (sigmaA_eq_betaFour h) ▸ hq

structure D1GlobalU (G : Type) [Group G] [Finite G] : Prop
    extends CFSG.AGLEmbeddingD2.AGLGlobal G where
  preSigma : rankThreeAschCoreLocal G 2

theorem _root_.CFSG.AGLEmbeddingD2.AGLGlobal.toD1Global (h : CFSG.AGLEmbeddingD2.AGLGlobal G)
    (h4 : 4 ≤ evenRank G) : D1Global G :=
  ⟨h.simple, h.nonab, h.kProper, h.charTwo, h4, h.pre⟩

instance : Coe (D1Global G) (CFSG.AGLEmbeddingD2.AGLGlobal G) := ⟨D1Global.toAGLGlobal⟩

theorem D1GlobalU.toD1Global (h : D1GlobalU G) (h4 : 4 ≤ evenRank G) : D1Global G :=
  h.toAGLGlobal.toD1Global h4

theorem D1Global.toU (h : D1Global G) : D1GlobalU G where
  toAGLGlobal := h.toAGLGlobal
  preSigma := fun p hp P => by
    have hp' : p ∈ GLBBetaFour G := mem_betaFour_of_mem_sigmaA h.rank hp
    exact (h.pre p hp').2 P

end CFSG.AGLEmbedding
