module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExotic
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSig

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem ysPPointTypeLinTwoOrUnitary_holds :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointTypeLinTwoOrUnitary :=
  ysPPointTypeLinTwoOrUnitary_of_kfacts (fun _ _ _ h => autRankTwoAt_of_exoticFive h)
    (fun _ _ _ h => signalizerAutAt_of_exoticFive h)

end CFSG.LocalAnalysis.RankFourTheoremC
