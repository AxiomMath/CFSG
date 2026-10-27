module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111E16

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81ElevenTwelveOne (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    3 ∈ rankThreeSigmaA G → AGL81CfgData 3 P M H Q K → IsAltTwoP 3 K →
    ¬ HasPrimeConstraint (G := H) 3 →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∃ I₀ ∈ cZero (H ⊓ L), CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre 3 H K) →
    Open.pRank 3 H ≤ 2

theorem agl81ElevenTwelveAtA6_of (h115 : AGL81ElevenFiveAt G)
    (h3σ : 3 ∈ rankThreeSigmaA G) (h101 : AGL81TenOneExists G)
    (h1112 : AGL81ElevenTwelveOne G) (hS : Setting G) {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hd : AGL81ElevenData 3 P M H Q K)
    (hA : IsAltTwoP 3 K) (hnc : ¬ HasPrimeConstraint (G := H) 3) : Open.pRank 3 H ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hb3 := hd.b3
  have hsy := hd.sylowK
  rw [hd.kbar] at hb3 hsy
  obtain ⟨L, hL⟩ :=
    h101 hS 3 P M H₁ R₁ hesc H Q hd.pair.base hd.pair.le_H hd.maxH hd.pair.not_le hsy hb3
  obtain ⟨-, -, h5⟩ := h115 hS 3 P M H Q K h3σ hd hnc (fun _ => by omega) L hL
  rcases h5 with ⟨-, hI⟩ | ⟨hL34, -⟩
  · exact absurd (h1112 hS P M H Q K h3σ hd.toCfg hA hnc L hL hI) (by omega)
  · have h1 := card_of_isAltTwoP_three hA
    have h2 := AGLEmbedding.card_of_isLinThreeFour hL34
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
