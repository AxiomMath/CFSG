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
@[expose] def CFSG.KD.NRT.c125223.P : Prs := tri [] n125223

#kc_plan CFSG.KD.NRT.c125223 "c125223.plan.txt" 1918 8241569479556941689
#kc_plan CFSG.KD.NRT.c125223 "c125223.grp.txt" 1009 10124863898744484116
#kc_select CFSG.KD.NRT.c125223 CH CH 49
#kc_select CFSG.KD.NRT.c125223 PRf PR 38
#kc_select CFSG.KD.NRT.c125223 GKf GK 49
#kc_listDispatch CFSG.KD.NRT.c125223 Gf G 6

namespace CFSG.KD.NRT.c125223

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c125223

#kc_each CFSG.KD.NRT.c125223.u 0 6

end
