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
@[expose] def CFSG.KD.NRT.c125556.P : Prs := tri e125556 []

@[expose] noncomputable def CFSG.KD.NRT.c125556.run := CFSG.KD.NRT.runP CFSG.KD.NRT.c125556.P

#kc_chain CFSG.KD.NRT.c125556 CFSG.KD.NRT.c125556.run "c125556.plan.txt" 2102 14976954023380108431
#kc_select CFSG.KD.NRT.c125556 Xf X 63
#kc_select CFSG.KD.NRT.c125556 Af A 63
#kc_select CFSG.KD.NRT.c125556 Wf W 63
#kc_select CFSG.KD.NRT.c125556 CH CH 66

namespace CFSG.KD.NRT.c125556

open CFSG.KC.KDense

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP P S (CH k)

end CFSG.KD.NRT.c125556

#kc_each CFSG.KD.NRT.c125556.t 0 66

end
