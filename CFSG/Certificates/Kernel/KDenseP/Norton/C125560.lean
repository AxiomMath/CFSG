module

public import CFSG.Certificates.Kernel.KDenseP.Norton.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
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
@[expose] def CFSG.KD.NRT.c125560.P : Prs := tri e125560 []

#kc_plan CFSG.KD.NRT.c125560 "c125560.plan.txt" 2814 8716429447146970988
#kc_plan CFSG.KD.NRT.c125560 "c125560.grp.txt" 1564 10730110115997620022
#kc_select CFSG.KD.NRT.c125560 CH CH 75
#kc_select CFSG.KD.NRT.c125560 PRf PR 57
#kc_select CFSG.KD.NRT.c125560 GKf GK 75
#kc_listDispatch CFSG.KD.NRT.c125560 Gf G 10

namespace CFSG.KD.NRT.c125560

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c125560

#kc_each CFSG.KD.NRT.c125560.u 0 10

end
