module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadPsp
public import CFSG.ClassicalInvolution.Q3.Q3AMPspG04

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

section Gen



theorem pspLayerGen_proved : PspLayerGenLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hset _ _ _ _ _ _ hax =>
    hset.bad.exactLayer3_le_rankTwoSpan_axis hset.intrinsic hset.nbrK hset.nbrJ hax

end Gen

end CFSG.ClassicalInvolution.Q3.Q3AM
