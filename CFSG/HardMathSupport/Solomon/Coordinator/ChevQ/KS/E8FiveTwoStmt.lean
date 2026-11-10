module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SevenWeylPair
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4Close
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

set_option linter.unusedSectionVars false

section Statements

abbrev LangE8Ten (K : Type) [Field K] [Finite K] : Type 1 :=
  LangLevi Tag.E8 K ((coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten)

end Statements

end Two

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
