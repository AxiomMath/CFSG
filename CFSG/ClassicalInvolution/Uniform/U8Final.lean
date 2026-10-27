module

public import CFSG.ClassicalInvolution.Uniform.U8Cover
public import CFSG.ClassicalInvolution.Uniform.U8Twist

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open hiding StatedLieTag StatedLieAdmissible


theorem excLayer3 : ExcLayer3 := by
  intro t n ht hadm
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact hasLayer3_F4 hadm
  · exact hasLayer3_E6 hadm
  · exact hasLayer3_E7 hadm
  · exact hasLayer3_E8 hadm
  · exact hasLayer3_twistedE6 hadm

theorem ih8TwinShapeU_proved : Ih8TwinShapeU :=
  ih8TwinShapeU_of_layer excLayer3

end CFSG.ClassicalInvolution.Uniform
