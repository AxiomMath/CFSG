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
@[expose] def CFSG.KD.NRT.c125501.P : Prs := tri e125501 n125501

#kc_plan CFSG.KD.NRT.c125501 "c125501.plan.txt" 3228 17667605948724984758
#kc_plan CFSG.KD.NRT.c125501 "c125501.grp.txt" 1792 10900200193670782124
#kc_select CFSG.KD.NRT.c125501 CH CH 86
#kc_select CFSG.KD.NRT.c125501 PRf PR 64
#kc_select CFSG.KD.NRT.c125501 GKf GK 86
#kc_listDispatch CFSG.KD.NRT.c125501 Gf G 12

namespace CFSG.KD.NRT.c125501

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c125501

#kc_each CFSG.KD.NRT.c125501.u 0 12

end
