module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf19Sect
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf14Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf14E8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf9Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf9Sev3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Fin12

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

structure TwinThmEInputs12 : Prop where
  exact : ExactO2Q8
  ae5 : AE5ExitQ8
  orbit4 : E187Orbit4Q8
  reduce : E189ReduceQ8'
  leaf : E189LeafQ8
  oddCore : E189OddCoreQ8
  ae5Branch : E189AE5Q8
  u3 : E178U3Q8

theorem thmEQ8_of_inputs12 (hT : T4Supply) (hD : D2Supply) (I : TwinThmEInputs12) : ThmEQ8 :=
  let o2 := e18_6O2Q8_of_D2 hD I.exact e8ExitQ8_proved I.ae5 (e18_5Q8_of_supply hT)
  let h6 := e18_6Q8_of_supply hT o2
  let h4 := e18_4CQ8_of_supply hT
  let h7 := e18_7Q8_of h6 h4 I.orbit4
  thmEQ8_of_minCexFalse
    (minCexFalseQ8_of_steps_C h6 (e18_8zQ8_of_e18_7 h7)
      (e18_9Q8_of' h6 h7 h4 I.reduce I.leaf I.oddCore I.ae5Branch)
      (e18_endQ8C_of (e178BenderQ8_of' I.u3)))

end Fin12

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
