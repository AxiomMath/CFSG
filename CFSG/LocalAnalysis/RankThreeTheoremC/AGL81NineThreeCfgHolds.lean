module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenFourL34Of
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeX

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem agl81NineThreeNormalCfg_holds : AGL81NineThreeNormalCfg G := by
  intro _ p P M H Q K hd
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hk := hd.kbar
  subst hk
  exact d1KBar_normal_of_escape he hd.base hd.le_H fun h => hd.not_le_X0 (by rw [h]; exact bot_le)

theorem agl81NineThreeRankCfg_holds : AGL81NineThreeRankCfg G := by
  intro _ p P M H Q K hd
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hk := hd.kbar
  subst hk
  exact pRank_d1PlusCore_le_one_of_escape he hd.base hd.le_H
    fun h => hd.not_le_X0 (by rw [h]; exact bot_le)

theorem agl81NineThreeXCfg_holds : AGL81NineThreeXCfg G := by
  intro _ p P M H Q K hd
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hk := hd.kbar
  subst hk
  exact d1PlusCore_le_of_escape he hd.base hd.le_H fun h => hd.not_le_X0 (by rw [h]; exact bot_le)

end CFSG.LocalAnalysis.RankThreeTheoremC
