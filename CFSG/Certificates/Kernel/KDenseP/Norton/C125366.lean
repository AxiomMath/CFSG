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
@[expose] def CFSG.KD.NRT.c125366.P : Prs := tri (tbChainPairs [4, 7]) []

#kc_plan CFSG.KD.NRT.c125366 "c125366.plan.txt" 7743 7782163685949239314
#kc_plan CFSG.KD.NRT.c125366 "c125366.grp.txt" 5411 7225381272456317152
#kc_select CFSG.KD.NRT.c125366 CH CH 225
#kc_select CFSG.KD.NRT.c125366 PRf PR 195
#kc_select CFSG.KD.NRT.c125366 GKf GK 225
#kc_listDispatch CFSG.KD.NRT.c125366 Gf G 33

namespace CFSG.KD.NRT.c125366

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c125366

#kc_each CFSG.KD.NRT.c125366.u 0 33

end
