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
@[expose] def CFSG.KD.NRT.c125500.P : Prs := tri e125500 []

@[expose] noncomputable def CFSG.KD.NRT.c125500.run := CFSG.KD.NRT.runP CFSG.KD.NRT.c125500.P

#kc_chain CFSG.KD.NRT.c125500 CFSG.KD.NRT.c125500.run "c125500.plan.txt" 1283 9282190791033470519
#kc_select CFSG.KD.NRT.c125500 Xf X 36
#kc_select CFSG.KD.NRT.c125500 Af A 36
#kc_select CFSG.KD.NRT.c125500 Wf W 36
#kc_select CFSG.KD.NRT.c125500 CH CH 39

namespace CFSG.KD.NRT.c125500

open CFSG.KC.KDense

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP P S (CH k)

end CFSG.KD.NRT.c125500

#kc_each CFSG.KD.NRT.c125500.t 0 39

end
