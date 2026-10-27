module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFW0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Mainouter




variable {n : ℕ}


section Main

theorem v3WFinalWg_of_B0 (hEW : TwinThmEW.ThmEQ8) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (hB0 : WFB0 n) :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.V3WFinalWg n :=
  v3WFinalWg_of_subleaves (wfW0_proved n) hB0 (wfStepC_of_leaves hB0 (wfWM_proved n) (wfD4_proved n))
    (wfStepD_of_B0 hEW hcit hP hB0)

end Main

end Mainouter

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
