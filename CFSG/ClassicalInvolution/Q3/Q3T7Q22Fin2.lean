module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22PsuPair
public import CFSG.ClassicalInvolution.Q3.Q3PsuSup3
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Psu

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

theorem psuLayerApi3_proved : Q3T8.Asc77.C22G.PsuLayerApi3 where
  pair := Q3T8.Asc77.C22G.psuLayer_pair3
  sup := by
    intro X _ Φ P K J J' RK RJ RJ' hRJ' hKR hJR hJ'R h1 h2 hc
    exact Q3PsuSup.psuLayer_sup3 P hRJ' hKR hJR hJ'R h1 h2 hc

end CFSG.ClassicalInvolution.Q3.Q3T7
