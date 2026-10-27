module

public import CFSG.Certificates.Kernel.KDenseP.E11.Run
public import CFSG.Certificates.Kernel.KDenseP.E11.Pairs16953
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.E11 in
@[expose] noncomputable def CFSG.KD.E11.c16953.run := CFSG.KD.E11.runP (tri e16953 [])

#kc_chain CFSG.KD.E11.c16953 CFSG.KD.E11.c16953.run "c16953.plan.txt" 8432 5336076420140026869
#kc_select CFSG.KD.E11.c16953 Xf X 144
#kc_select CFSG.KD.E11.c16953 Af A 144
#kc_select CFSG.KD.E11.c16953 Wf W 144
#kc_select CFSG.KD.E11.c16953 CH CH 216

namespace CFSG.KD.E11.c16953

open CFSG.KC.KDense CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.E11

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP (tri e16953 []) S (CH k)

end CFSG.KD.E11.c16953

#kc_each CFSG.KD.E11.c16953.t 0 216

end
