module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6Uniq
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerComp

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

set_option linter.unusedSectionVars false


theorem bal209TwoSLOBIn_of_bal207 (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) :
    Bal209TwoSLOBIn :=
  bal209TwoSLOBIn_of_compType h207 bal209TwoInnerCompType_holds

theorem bal209Two_of_bal207 (h207 : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) : Bal209Two :=
  bal209Two_of_inner bal209TwoUniqIn_holds (bal209TwoSLOBIn_of_bal207 h207)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
