module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25ZFin4
public import CFSG.ClassicalInvolution.Q3.Q3T7P25UFin
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YOFin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P25



theorem c25_E4Three_proved : Q3T7.C25_E4Three :=
  c25_E4Three_of_parity
    (parityE4Three_of_om6ReflDiag nc4Fact3_proved Q3T8.Asc77.CX.om6ReflDiag_proved)

end CFSG.ClassicalInvolution.Q3.Q3T7P25
