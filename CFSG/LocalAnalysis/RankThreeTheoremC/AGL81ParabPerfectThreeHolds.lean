module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabPerfectThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ParabThreeInv

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding


theorem kFactParabolicPerfectThree_holds : KFactParabolicPerfectThree :=
  kFactParabolicPerfectThree_of kFactParabolicThreeInv_holds

end CFSG.LocalAnalysis.RankThreeTheoremC
