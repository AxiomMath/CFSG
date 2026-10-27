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
@[expose] def CFSG.KD.NRT.c125221.P : Prs := tri e125221 []

@[expose] noncomputable def CFSG.KD.NRT.c125221.run := CFSG.KD.NRT.runP CFSG.KD.NRT.c125221.P

#kc_chain CFSG.KD.NRT.c125221 CFSG.KD.NRT.c125221.run "c125221.plan.txt" 3145 12857639991919511472
#kc_select CFSG.KD.NRT.c125221 Xf X 87
#kc_select CFSG.KD.NRT.c125221 Af A 87
#kc_select CFSG.KD.NRT.c125221 Wf W 87
#kc_select CFSG.KD.NRT.c125221 CH CH 96

namespace CFSG.KD.NRT.c125221

open CFSG.KC.KDense

@[expose] noncomputable def S (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (Xf j) (Af j) (Wf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def t (k : Nat) : Bool := chkP P S (CH k)

end CFSG.KD.NRT.c125221

#kc_each CFSG.KD.NRT.c125221.t 0 96

end
