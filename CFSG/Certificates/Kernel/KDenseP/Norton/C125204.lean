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
@[expose] def CFSG.KD.NRT.c125204.P : Prs := tri (nodeQPairs 1) []

#kc_plan CFSG.KD.NRT.c125204 "c125204.plan.txt" 3486 3357995917577889514
#kc_plan CFSG.KD.NRT.c125204 "c125204.grp.txt" 1820 6416512901975601908
#kc_select CFSG.KD.NRT.c125204 CH CH 90
#kc_select CFSG.KD.NRT.c125204 PRf PR 63
#kc_select CFSG.KD.NRT.c125204 GKf GK 90
#kc_listDispatch CFSG.KD.NRT.c125204 Gf G 10

namespace CFSG.KD.NRT.c125204

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c125204

#kc_each CFSG.KD.NRT.c125204.u 0 10

end
