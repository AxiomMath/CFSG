module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.D4Centre
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnit
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrth
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.D4Block
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcAssembly

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.Yardstones.Md42047359a2a

set_option linter.unusedSectionVars false

theorem nonD4LieContraOn_suzukiReeTits : NonD4LieContraOn .suzukiReeTits :=
  nonD4LieContraOn_of_simple nonD4LieContraS_suzukiReeTits

theorem input14_33TypeSameField_of_open (hSpor : ∀ s, SporL3Down s) (hLie : LieL3Down)
    (hF4 : NonD4LieContraOnF4TwoOdd) :
    Input14_33TypeSameField :=
  input14_33TypeSameField_of_leaves hSpor hLie d4CentreTrivial_holds d4FieldSharp_holds
    (nonD4LieContraOn_of_simple nonD4LieContraS_linearUnitary)
    (nonD4LieContraOn_of_simple nonD4LieContraS_symplecticOrthogonal)
    (nonD4LieContraOn_exceptional_of_residual hF4) nonD4LieContraOn_suzukiReeTits

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
