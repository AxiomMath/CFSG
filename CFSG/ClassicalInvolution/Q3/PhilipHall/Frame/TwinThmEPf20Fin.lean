module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf19Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf14Exact
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf20Leaf

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Fin15

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

structure TwinThmEInputs15 : Prop where
  orbit4 : E187Orbit4Q8
  reduce : E189ReduceQ8'
  ae5Branch : E189AE5Q8
  e4 : E189E4ModelT
  u3 : E178U3Q8

theorem thmEQ8_of_inputs15 (hT : T4Supply) (hD : D2Supply) (I : TwinThmEInputs15) : ThmEQ8 :=
  thmEQ8_of_inputs12 hT hD
    ⟨exactO2Q8_proved, ae5ExitQ8_proved, I.orbit4, I.reduce, e189LeafQ8_of' I.e4, e189OddCoreQ8_proved,
      I.ae5Branch, I.u3⟩

end Fin15

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
