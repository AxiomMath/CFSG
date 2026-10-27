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

open CFSG.KC.KDenseP.Norton CFSG.AGLEmbedding.Norton.MON5_7 in
@[expose] def CFSG.KD.NRT.c125222.P : Prs := tri sevenGPairs []

#kc_plan CFSG.KD.NRT.c125222 "c125222.plan.txt" 909 14559731454090091854
#kc_plan CFSG.KD.NRT.c125222 "c125222.grp.txt" 492 385284846510893244
#kc_select CFSG.KD.NRT.c125222 CH CH 24
#kc_select CFSG.KD.NRT.c125222 PRf PR 21
#kc_select CFSG.KD.NRT.c125222 GKf GK 24
#kc_listDispatch CFSG.KD.NRT.c125222 Gf G 3

namespace CFSG.KD.NRT.c125222

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c125222

#kc_each CFSG.KD.NRT.c125222.u 0 3

end
