module

public import CFSG.Certificates.Kernel.KDenseP.Norton.Run
public import CFSG.Certificates.Kernel.Common.Chain
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.D13CheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ElevenCheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenCheckDefs
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON11_13.ThirteenEligibleDefs
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

open CFSG.KC.KDenseP.Norton in
@[expose] def CFSG.KD.NRT.c125559.P : Prs := tri e125559 []

@[expose] noncomputable def CFSG.KD.NRT.c125559.run := CFSG.KD.NRT.runP CFSG.KD.NRT.c125559.P

#kc_chain CFSG.KD.NRT.c125559 CFSG.KD.NRT.c125559.run "c125559.plan.txt" 2357 10898404326941328771
#kc_select CFSG.KD.NRT.c125559 Xf X 66
#kc_select CFSG.KD.NRT.c125559 Af A 66
#kc_select CFSG.KD.NRT.c125559 Wf W 66
#kc_select CFSG.KD.NRT.c125559 CH CH 72

namespace CFSG.KD.NRT.c125559

open CFSG.KC.KDense

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP P S (CH k)

end CFSG.KD.NRT.c125559

#kc_each CFSG.KD.NRT.c125559.t 0 72

end
