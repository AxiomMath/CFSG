module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.Dispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435Chev.TwistedD4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6

section Holds


theorem kFact1435ChevTwo_holds : KFact1435ChevTwo :=
  I1435Chev.kFact1435ChevTwo_of_twistedD4 fun q hq => I1435Chev.familyAt_twistedD4 q hq

theorem kFact1435_holds : KFact1435 :=
  kFact1435_of_chevTwo kFact1435ChevTwo_holds

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.A6
