module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottKGGOmPlusMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG


theorem kgNoncycCent_holds : KGNoncycCent :=
  kgNoncycCent_of_gen ParrottKGGOmPlus.kgConclPOmegaPlus_holds kgConclE6_holds

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
