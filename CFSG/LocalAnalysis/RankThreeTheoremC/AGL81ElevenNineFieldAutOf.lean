module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeNormalRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem AGL81ElevenNineData.pRank_jZero_le_one {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {L W : Subgroup G} {a₀ : G}
    (hd : AGL81ElevenNineData p P M H Q K L W a₀) : Open.pRank p (jZero H L) ≤ 1 := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.data.escape
  have hKne : d1KBar p M H ≠ ⊥ := by
    rw [← hd.data.kbar]
    exact fun h => hd.data.not_le_X0 (h ▸ bot_le)
  refine (CFSG.SectionRank.pRank_mono hesc.prime.one_lt hd.j0_le).trans ?_
  rw [hd.data.kbar]
  exact pRank_d1PlusCore_le_one_of_escape hesc hd.data.base hd.data.le_H hKne

end CFSG.LocalAnalysis.RankThreeTheoremC
