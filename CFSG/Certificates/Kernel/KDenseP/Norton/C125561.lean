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
@[expose] def CFSG.KD.NRT.c125561.P : Prs := tri e125561 []

@[expose] noncomputable def CFSG.KD.NRT.c125561.run := CFSG.KD.NRT.runP CFSG.KD.NRT.c125561.P

#kc_chain CFSG.KD.NRT.c125561 CFSG.KD.NRT.c125561.run "c125561.plan.txt" 2085 15563483113295902061
#kc_select CFSG.KD.NRT.c125561 Xf X 57
#kc_select CFSG.KD.NRT.c125561 Af A 57
#kc_select CFSG.KD.NRT.c125561 Wf W 57
#kc_select CFSG.KD.NRT.c125561 CH CH 63

namespace CFSG.KD.NRT.c125561

open CFSG.KC.KDense

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP P S (CH k)

end CFSG.KD.NRT.c125561

#kc_each CFSG.KD.NRT.c125561.t 0 63

end
