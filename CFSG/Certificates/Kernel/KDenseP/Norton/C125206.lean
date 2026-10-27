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

open CFSG.KC.KDenseP.Norton CFSG.AGLEmbedding.Norton.MON5_7 in
@[expose] def CFSG.KD.NRT.c125206.P : Prs := tri [] n125206

@[expose] noncomputable def CFSG.KD.NRT.c125206.run := CFSG.KD.NRT.runP CFSG.KD.NRT.c125206.P

#kc_chain CFSG.KD.NRT.c125206 CFSG.KD.NRT.c125206.run "c125206.plan.txt" 325 5110175374313150566
#kc_select CFSG.KD.NRT.c125206 Xf X 3
#kc_select CFSG.KD.NRT.c125206 Af A 3
#kc_select CFSG.KD.NRT.c125206 Wf W 3
#kc_select CFSG.KD.NRT.c125206 CH CH 6

namespace CFSG.KD.NRT.c125206

open CFSG.KC.KDense

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP P S (CH k)

end CFSG.KD.NRT.c125206

#kc_each CFSG.KD.NRT.c125206.t 0 6

end
