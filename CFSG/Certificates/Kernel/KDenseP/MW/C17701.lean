module

public import CFSG.Certificates.Kernel.KDenseP.MW.Run
public import CFSG.HardMathSupport.Dickson.BMRows.M11SylowInputs
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.MonThreeB CFSG.HardMathSupport.Dickson.BMRows.M11 in
@[expose] noncomputable def CFSG.KD.MW.c17701.run := CFSG.KD.MW.runP (tri m11Pairs [])

#kc_chain CFSG.KD.MW.c17701 CFSG.KD.MW.c17701.run "c17701.plan.txt" 2106 4423533108185452607
#kc_select CFSG.KD.MW.c17701 Xf X 36
#kc_select CFSG.KD.MW.c17701 Af A 36
#kc_select CFSG.KD.MW.c17701 Wf W 36
#kc_select CFSG.KD.MW.c17701 CH CH 54

namespace CFSG.KD.MW.c17701

open CFSG.KC.KDense CFSG.KC.KDenseP.MonThreeB CFSG.HardMathSupport.Dickson.BMRows.M11

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri m11Pairs []) S (CH k)

end CFSG.KD.MW.c17701

#kc_each CFSG.KD.MW.c17701.t 0 54

end
