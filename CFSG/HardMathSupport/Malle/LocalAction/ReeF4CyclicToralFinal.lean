module

public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4CaseTwoInputs
public import CFSG.HardMathSupport.Malle.LocalAction.ReeF4CyclicTorusCentralizer

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

theorem reeF4CyclicToralCentralizers_of_certs :
    Coordinator.ReeF4CyclicToralCentralizers :=
  reeF4CyclicToralCentralizers_of_regular_certs
    (by intro K _ _ _ hK; exact exists_regular_element_13 hK)
    (by intro K _ _ _ hK; exact exists_regular_element_61 hK)
    (by intro K _ _ _ hK; exact exists_regular_element_331 hK)
    (by intro K _ _ _ hK; exact exists_regular_element_1321 hK)

end CFSG.HardMathSupport.Malle.LocalAction
