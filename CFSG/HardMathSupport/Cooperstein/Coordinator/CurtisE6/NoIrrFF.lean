module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Reduction
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Surv78
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExcFamilies

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6


theorem coopersteinNoIrrFFE6 : CoopersteinNoIrrFFE6 := fun q hv hq =>
  noIrrFFOffender_E6_of_interfaces e6Surv27_holds e6Surv78_holds e6InnerOfSqOne_holds q hv hq

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
