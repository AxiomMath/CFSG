module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoMain

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


theorem nonD4LieContraOnF4TwoOdd_holds : NonD4LieContraOnF4TwoOdd :=
  nonD4LieContraOnF4TwoOdd_of_model fun n hn F _ _ hF x g y J =>
    not_innerHeisCfg_F4 n hn F hF x g y J

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
