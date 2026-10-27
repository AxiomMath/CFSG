module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneCoset
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToral
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneWeyl

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

set_option linter.unusedSectionVars false

section Plane


theorem e6ThreeNotAll24NFA_of_census : E6NotAll24Census → E6ThreeNotAll24NFA :=
  fun hC => e6ThreeNotAll24NFA_of_stmts e6PlaneCoset_proved e6PlaneToral_proved
    e6PlaneWeyl_proved hC

end Plane

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
