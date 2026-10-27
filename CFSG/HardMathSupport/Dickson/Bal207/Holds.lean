module

public import CFSG.HardMathSupport.Dickson.Bal207.Closed
public import CFSG.HardMathSupport.Dickson.Bal207.D42Triality

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux

section Holds

set_option linter.unusedSectionVars false

theorem bal207Corr_holds : Bal207Corr :=
  bal207Corr_of_triality D42Tri.d42TrialityShape_proved

theorem bal207D4_holds : OuterFourAux.Bal207D4 IsGraphAutFour :=
  bal207D4_of_triality D42Tri.d42TrialityShape_proved

end Holds

end CFSG.HardMathSupport.Dickson.Bal207

end
