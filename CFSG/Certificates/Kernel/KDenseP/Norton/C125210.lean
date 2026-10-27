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
@[expose] def CFSG.KD.NRT.c125210.P : Prs := tri sevenOrderPairs []

#kc_plan CFSG.KD.NRT.c125210 "c125210.plan.txt" 2047 2561518439853113014
#kc_plan CFSG.KD.NRT.c125210 "c125210.grp.txt" 1330 15716367609320416077
#kc_select CFSG.KD.NRT.c125210 CH CH 60
#kc_select CFSG.KD.NRT.c125210 PRf PR 54
#kc_select CFSG.KD.NRT.c125210 GKf GK 60
#kc_listDispatch CFSG.KD.NRT.c125210 Gf G 9

namespace CFSG.KD.NRT.c125210

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c125210

#kc_each CFSG.KD.NRT.c125210.u 0 9

end
