module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockPerfectCoreThreeSmall
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

theorem kFactCompParabPerfectCoreThree_of_families
    (hA : KFactCompParabPerfectCoreThreeOn (IsLieOf IdxA))
    (h2A : KFactCompParabPerfectCoreThreeOn (IsLieOf IdxTwistedA))
    (hB : KFactCompParabPerfectCoreThreeOn (IsLieOf IdxB))
    (hD : KFactCompParabPerfectCoreThreeOn (IsLieOf IdxD))
    (h2D : KFactCompParabPerfectCoreThreeOn (IsLieOf IdxTwistedD))
    (hG : KFactCompParabPerfectCoreThreeOn (IsLieOf IdxG2))
    (hS : KFactCompParabPerfectCoreThreeOn IsSmallTwoOrG2) : KFactCompParabPerfectCoreThree := by
  intro Y _ _ L P hCP
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  exacts [hA Y L P hCP h, h2A Y L P hCP h, hB Y L P hCP h, hD Y L P hCP h, h2D Y L P hCP h,
    hG Y L P hCP h, hS Y L P hCP h]

theorem kFactCompParabPerfectCoreThree_of_griess
    (hGA : GriessAllModelsStatement) : KFactCompParabPerfectCoreThree := by
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  exact kFactCompParabPerfectCoreThree_of_families
    (kFactCompParabPerfectCoreThreeOn_linear hGA) kFactCompParabPerfectCoreThreeOn_twistedA
    (kFactCompParabPerfectCoreThreeOn_idxB hZ) (kFactCompParabPerfectCoreThreeOn_idxD hZ)
    (kFactCompParabPerfectCoreThreeOn_twistedD hZ) (kFactCompParabPerfectCoreThreeOn_g2 hGA)
    (kFactCompParabPerfectCoreThreeOn_small hGA)

theorem kFactBlockPerfectCoreThree_of_griess
    (hGA : GriessAllModelsStatement) : KFactBlockPerfectCoreThree :=
  kFactBlockPerfectCoreThree_of (kFactCompParabPerfectCoreThree_of_griess hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
