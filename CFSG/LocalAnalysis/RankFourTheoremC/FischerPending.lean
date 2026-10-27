module

public import CFSG.LocalAnalysis.RankFourTheoremC.FullCoreRank4
public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Obstruction
public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.PConstrained
public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Rank
public import CFSG.LocalAnalysis.RankFourTheoremC.FischerPending.Transitivity
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem ObstructionSetting.of_d1Global (hS : D1Global G) : ObstructionSetting G where
  charTwo := hS.charTwo
  exists_core p hp P := by
    obtain ⟨Y, hY, hWY⟩ := (hS.pre p (mem_betaFour_of_mem_sigmaA hS.rank hp)).2 P
    obtain ⟨M, hYM, hM⟩ := exists_maximal_twoLocal hY
    exact ⟨M, hM, hWY.trans hYM⟩
  three_le_pRank p hp P := by
    have := four_le_pRank_sylow (mem_betaFour_of_mem_sigmaA hS.rank hp) P
    omega

theorem fischerRankFourPending (G : Type) [Group G] [Finite G] : FischerRankFourPending G where
  exists_extremal_obstruction hS hD1 hfail :=
    (ObstructionSetting.of_d1Global hS).exists_extremal_obstruction hD1 hfail
  transitivityCase hS hD1 hR h13 hX :=
    have hO := ObstructionSetting.of_d1Global hS
    hO.transitivityCase_of_containment hD1 hR h13
      (hO.gl83InvariantTwoContainment_of_relativePairExclusion hD1 hR h13 hX)
  le_of_isPConstrained := by
    intro hS p hp P M D hext hPD H hPH hH
    exact (ObstructionSetting.of_d1Global hS).le_of_isPConstrained hp hext hPD hPH hH

end CFSG.LocalAnalysis.RankFourTheoremC
