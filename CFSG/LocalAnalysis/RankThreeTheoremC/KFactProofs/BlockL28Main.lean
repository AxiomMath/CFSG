module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Lin
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Uni
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Symp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28SympTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28OrthPlus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28OrthMinus
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28G2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Small
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

theorem kFactCompParabL28Rank_of_griess
    (hGA : GriessAllModelsStatement) :
    KFactCompParabL28Rank := by
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  exact kFactCompParabL28Rank_of_families (kFactCompParabL28RankOn_linear hGA)
    kFactCompParabL28RankOn_twistedA (kFactCompParabL28RankOn_idxB hZ)
    (kFactCompParabL28RankOn_idxD hZ) (kFactCompParabL28RankOn_twistedD hZ)
    (kFactCompParabL28RankOn_g2 hGA) (kFactCompParabL28RankOn_small hZ)

theorem kFactCompParabL28TwoRank_of_griess
    (hGA : GriessAllModelsStatement) :
    KFactCompParabL28TwoRank := by
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  exact kFactCompParabL28TwoRank_of_families (kFactCompParabL28TwoRankOn_linear hGA)
    kFactCompParabL28TwoRankOn_twistedA (kFactCompParabL28TwoRankOn_idxB hZ)
    (kFactCompParabL28TwoRankOn_idxD hZ) (kFactCompParabL28TwoRankOn_twistedD hZ)
    (kFactCompParabL28TwoRankOn_g2 hGA) (kFactCompParabL28TwoRankOn_small hZ)

theorem kFactBlockL28Rank_of_griess
    (hGA : GriessAllModelsStatement) :
    KFactBlockL28Rank :=
  kFactBlockL28Rank_of (kFactCompParabL28Rank_of_griess hGA)

theorem kFactBlockL28TwoRank_of_griess
    (hGA : GriessAllModelsStatement) :
    KFactBlockL28TwoRank :=
  kFactBlockL28TwoRank_of (kFactCompParabL28TwoRank_of_griess hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
