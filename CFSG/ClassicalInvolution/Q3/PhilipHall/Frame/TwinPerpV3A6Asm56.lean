module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6Asm52
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Final
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SAE8Proof
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertBAE8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6CertC2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6gMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h1Par

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


theorem v3AE6I23_proved
    (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n) : V3AE6I23 n := by
  have hC : V3AE6EComm n := A6c.v3AE6EComm_of A6b.v3AE6E_proved
  have hDN : V3AE6DNorm n := A6DN.v3AE6DNorm_proved hC
  have hI : V3AE6I n := A6d.v3AE6I_of_c hP (v3AE6D_of A6b.v3AE6E_proved hC) hDN
  exact A6g.v3AE6I23_of hP hC hDN hI (A6f.v3AE6E3_of hC hDN hI) (A6f.v3AE6L_of_parts hP hC hDN hI)
    A6h1.ae6ModelPar_proved

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6Asm
