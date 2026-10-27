module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Asm50
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cFinal
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6fMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelQ8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelFW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SFProof

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Asm

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}


theorem v3ExitAE6WfN_of_parts52
    (hEW : TwinThmEW.ThmEQ8) (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (hSec : SecEdgelessConcl163 n) (hSec4 : SecTwinNoRoot n) (hGenExC : V3LayerGenExConjAd n)
    (hOpen : V3SecOpenW n) (hPar : A6h1.AE6ModelPar) (h23 : V3AE6I23 n) (hGl : V3AE6Glue n)
    (hFF : AE6FFin) (hCS : AE6C2Search) : V3ExitAE6WfN n := by
  have hC : V3AE6EComm n := A6c.v3AE6EComm_of A6b.v3AE6E_proved
  have hDN : V3AE6DNorm n := A6DN.v3AE6DNorm_proved hC
  have hI : V3AE6I n := A6d.v3AE6I_of_c hP (v3AE6D_of A6b.v3AE6E_proved hC) hDN
  exact v3ExitAE6WfN_of_parts50 hEW hE hcit hP h4 hSp hD4 hM12 hSec hSec4 hGenExC hOpen hC
    (A6f.v3AE6L_of_parts hP hC hDN hI) hPar h23 hGl ae6ModelQ8_proved ae6ModelFW_proved
    (ae6ModelF_of_fin hFF) (ae6ModelC2_of_search hCS)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Asm
