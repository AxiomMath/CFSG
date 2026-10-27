module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalAdapter
public import CFSG.LocalAnalysis.OddStandard.AltStdBalCMain

public section

namespace CFSG.OddStandard.AltStdBal

theorem altStdCyclicBalancedFalse_of_order2 (h2 : AltStdBalancedOrder2) :
    AltStdCyclicBalancedFalse :=
  altStdCyclicBalancedFalse_of_order2_big h2 altStdBalancedBig_holds

theorem altStdCyclicBalancedFalse_of_inner_outer (hI : AltStdBalancedOrder2Inner)
    (hO : AltStdBalancedOrder2Outer) : AltStdCyclicBalancedFalse :=
  altStdCyclicBalancedFalse_of_order2 (altStdBalancedOrder2_of_inner_outer hI hO)

end CFSG.OddStandard.AltStdBal
