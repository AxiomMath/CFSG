module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22M11
public import CFSG.ClassicalInvolution.Q3.Q3M11NoInv

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77


theorem m11NoInverted3_proved : M11NoInverted3 := by
  intro X _ _ Φ hS _ hM H _ _ ι hι a _ ha _ A hA z hzA haA _ ha2 _ _
  exact Q3.m11NoInverted_core hS.gen hM ι hι a ha hA hzA haA ha2

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S16
