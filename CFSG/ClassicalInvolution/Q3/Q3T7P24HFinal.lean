module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24Final
public import CFSG.ClassicalInvolution.Q3.Q3T7P24H02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7P24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3T7

section Inputs


@[expose] def Hyp51Three : Prop := Hyp51VertexThree ∧ Hyp51TwinInnerThree

theorem h3_of_inputs (h23 : Sup23_2Three) (h51 : Hyp51Three) : H3Three := by
  have : Fact Sup23_2Three := ⟨@h23⟩
  have : Fact Hyp51VertexThree := ⟨@h51.1⟩
  have : Fact Hyp51TwinInnerThree := ⟨@h51.2⟩
  exact Q3T8.Asc77.S24B.h3_proved

theorem c24_1Three_of_inputs (h23 : Sup23_2Three) (h51 : Hyp51Three) : C24_1Three :=
  c24_1Three_of_h3 (h3_of_inputs h23 h51)

end Inputs

end CFSG.ClassicalInvolution.Q3.Q3T7P24
