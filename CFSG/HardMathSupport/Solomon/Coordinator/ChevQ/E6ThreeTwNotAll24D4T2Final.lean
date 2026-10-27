module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2TorusMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Coset
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2SpinPerfect
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2CentralTorus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Final

set_option linter.unusedSectionVars false

theorem d4t2TorusPart_holds : D4T2TorusPart :=
  d4t2TorusPart_of_spinPerfect d4t2_fixedSpinPerfect

theorem d4t2CosetPart_holds :
    D4T2CosetPart :=
  d4t2CosetPart_of_centralTorus d4t2CentralTorus_holds

theorem d4t2ModelGen_holds :
    D4T2ModelGen :=
  d4t2ModelGen_of_parts d4t2TorusPart_holds d4t2CosetPart_holds

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
