module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XExc2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2TriD4Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107X2TwF4Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X


theorem twoRankLowExcRest2_holds : TwoRankLowExcRest2 := by
  unfold TwoRankLowExcRest2
  intro S _ _ lab hS hrk _ _ htag
  rcases htag with ht | ht | ht | ht
  · exact CFSG.LocalAnalysis.GLTheoremA.I107X2.twoRankLow_triD4_holds S lab hS hrk ht
  · exact CFSG.LocalAnalysis.GLTheoremA.I107X2.twoRankLow_F4_holds S lab hS hrk ht
  · exact CFSG.LocalAnalysis.GLTheoremA.I107X2.twoRankLow_twF4_holds S lab hS hrk ht
  · exact CFSG.LocalAnalysis.GLTheoremA.I107X2.twoRankLow_twE6_holds S lab hS hrk ht

end CFSG.LocalAnalysis.GLTheoremA.I107X

end
