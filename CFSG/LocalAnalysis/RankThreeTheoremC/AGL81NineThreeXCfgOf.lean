module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111SizeMax
import CFSG.LocalAnalysis.RankThreeTheoremC.D2Ambient3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

variable {G : Type} [Group G] [Finite G]

theorem agl81NineThreeXCfg_of (h9 : AGL81NineCompetitorQ G) : AGL81NineThreeXCfg G := by
  intro hS p P M H Q K hd
  have hk := hd.kbar
  subst hk
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hne : d1KBar p M H ≠ ⊥ := fun h => hd.not_le_X0 (by rw [h]; exact bot_le)
  exact (h9 (aglGlobal_of_setting hS) p P M H (muAt_of_escape hesc) hd.maxH hd.not_le
    (exists_component_of_d1KBar_ne_bot hne) Q H hd.base hd.le_H hd.maxH hd.not_le hd.le_H
    (aglCovers_self H _)).1.nineThree.plusCore_le

end CFSG.LocalAnalysis.RankThreeTheoremC
