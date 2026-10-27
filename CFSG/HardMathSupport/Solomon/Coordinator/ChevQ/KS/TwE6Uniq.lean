module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqLang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqRat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.Bal209TwoInner

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

set_option linter.unusedSectionVars false


theorem bal209TwoUniq_holds : Bal209TwoUniq :=
  TwE6UniqAbs.bal209TwoUniq_of_model
    (TwE6UniqAbs.twE6UniqModel_of_ratQuasiEq TwE6UniqAbs.ratQuasiEq_holds)

theorem bal209TwoUniqIn_holds : Bal209TwoUniqIn :=
  bal209TwoUniqIn_of_uniq bal209TwoUniq_holds

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
