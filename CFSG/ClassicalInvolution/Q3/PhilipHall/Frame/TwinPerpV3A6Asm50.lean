module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6dOrb
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CentE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6NoWt1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6jB
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ModelSmall

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


theorem v3ExitAE6WfN_of_parts50
    (hEW : TwinThmEW.ThmEQ8) (hE : TwinThmE.TwinThmEP n) (hcit : CIT3Below n)
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) (h4 : Thm4RTwinBelow 3 n)
    (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM12 : ModelFactM12)
    (hSec : SecEdgelessConcl163 n) (hSec4 : SecTwinNoRoot n) (hGenExC : V3LayerGenExConjAd n)
    (hOpen : V3SecOpenW n) (hC : V3AE6EComm n) (hL : V3AE6L n) (hPar : A6h1.AE6ModelPar)
    (h23 : V3AE6I23 n) (hGl : V3AE6Glue n) (hQ8 : AE6ModelQ8) (hFW : AE6ModelFW) (hF : AE6ModelF)
    (hC2 : AE6ModelC2) : V3ExitAE6WfN n := by
  have hAb' := v3AbelianO2_of_tr h4 (v3AbelianO2Tr_of_split (v3AbelianO2TrS3_of_edgeless hSec)
    (v3AbelianO2TrG4_of_noRoot' hP hcit hSec4))
  have hU3 := v3Hyp51U3E8_of_abelianO2 hAb'
  have hB := v3Hyp51B_of_vertices (v3Hyp51U_of_model hSp hD4 hM12 h4 hU3)
  have hStarF := v3Hyp51StarF_of_model hSp hD4 hM12 h4
  have hαF := v3FourthAlphaF_of_star hB hStarF
  have h5 := v3Fourth_of_alphaF hαF
  have h7 := v3Alpha1_of_partsWAllC hEW hcit hP h4 hB h5 hαF hStarF
    (v3LayerGenAllC_of_exitConj hcit hP h4 hGenExC)
  have hD : V3AE6D n := v3AE6D_of A6b.v3AE6E_proved hC
  have hDN : V3AE6DNorm n := A6DN.v3AE6DNorm_proved hC
  have hI : V3AE6I n := A6d.v3AE6I_of_c hP hD hDN
  exact v3ExitAE6WfN_of_parts hEW hE hcit hP hSp hD4 h4 hB h5 h7 hOpen
    (A6e.v3AE6H_of hEW hcit hP h4 h5 h7 hOpen hD hDN hI) h23 (A6h1.v3AE6Shape_of hI hL hPar) hGl
    (A6NoWt1.v3AE6OmegaHA_of_models hQ8 ae6ModelSmall_proved hFW hF ae6ModelC1_inv_proved hC2
      ae6ModelC3_proved)
    (A6jB.v3AE6OmegaHB_of hQ8)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Asm
