module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoOfSevenPairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.ThreeFourTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen


open CFSG.HardMathSupport.Solomon.Coordinator in
theorem kFactThreeFourTwo_holds (hb : LieOrderBridge) (hOrd : SporadicOrdersTable)
    (hON : ONPair.OnanNQOvergroups) : KFactThreeFourTwo :=
  kFactThreeFourTwo_of_sevenPairs (threeFourTwoAt_onan hON)
    (Fi24K.threeFourTwoAt_fi24Prime_of_isKGroup hb hOrd)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
