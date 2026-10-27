module

public import CFSG.ClassicalInvolution.Q3.Q3AMTriT03
public import CFSG.ClassicalInvolution.Q3.Q3AMPspLeaves

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

section Top

theorem c28_triB_of_minimal
    (hTab : PspTableLeaf) (h9 : PspVertexSLeaf9)
    (hS4 : PspS4Leaf) (hD : C28_DoubleB) : C28_TriB :=
  c28_triB_of_leaves hTab (pspClose_of_vertexS9' h9) hS4 hD pspTripleLeaf_proved

end Top

end CFSG.ClassicalInvolution.Q3.Q3AM
