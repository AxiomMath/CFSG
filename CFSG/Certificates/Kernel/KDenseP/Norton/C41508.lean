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

namespace CFSG.KC.KDenseP.Norton

open CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.Gen11

@[expose] def e41508 : Prs := [(gen11W1 ++ gen11W3, gen11W3 ++ powL 8 gen11W0)]

end CFSG.KC.KDenseP.Norton

open CFSG.KC.KDenseP.Norton in
@[expose] def CFSG.KD.NRT.c41508.P : Prs := tri e41508 []

#kc_plan CFSG.KD.NRT.c41508 "c41508.plan.txt" 748 12775946233862830003
#kc_plan CFSG.KD.NRT.c41508 "c41508.grp.txt" 451 15291624462290140889
#kc_select CFSG.KD.NRT.c41508 CH CH 21
#kc_select CFSG.KD.NRT.c41508 PRf PR 21
#kc_select CFSG.KD.NRT.c41508 GKf GK 21
#kc_listDispatch CFSG.KD.NRT.c41508 Gf G 3

namespace CFSG.KD.NRT.c41508

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c41508

#kc_each CFSG.KD.NRT.c41508.u 0 3

end
