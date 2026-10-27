module

public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.E7Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExcFamilies

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis

open CFSG.HardMathSupport.Cooperstein.Coordinator


theorem coopersteinNoIrrFFE7 : CoopersteinNoIrrFFE7 :=
  fun q hv hq => noIrrFFOffender_E7 q hv hq

end CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis
