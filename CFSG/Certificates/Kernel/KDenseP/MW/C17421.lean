module

public import CFSG.Certificates.Kernel.KDenseP.MW.Run
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Inputs
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.MonThreeB CFSG.HardMathSupport.Dickson.I271 in
@[expose] noncomputable def CFSG.KD.MW.c17421.run := CFSG.KD.MW.runP (tri m13Pairs [])

#kc_chain CFSG.KD.MW.c17421 CFSG.KD.MW.c17421.run "c17421.plan.txt" 1344 4013730883745203040
#kc_select CFSG.KD.MW.c17421 Xf X 27
#kc_select CFSG.KD.MW.c17421 Af A 27
#kc_select CFSG.KD.MW.c17421 Wf W 27
#kc_select CFSG.KD.MW.c17421 CH CH 36

namespace CFSG.KD.MW.c17421

open CFSG.KC.KDense CFSG.KC.KDenseP.MonThreeB CFSG.HardMathSupport.Dickson.I271

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri m13Pairs []) S (CH k)

end CFSG.KD.MW.c17421

#kc_each CFSG.KD.MW.c17421.t 0 36

end
