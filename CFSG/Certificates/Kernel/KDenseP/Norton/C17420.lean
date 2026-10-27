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

@[expose] def e17420 : Prs := [(gen11W1 ++ gen11W4, gen11W4 ++ powL 3 gen11W1)]

end CFSG.KC.KDenseP.Norton

open CFSG.KC.KDenseP.Norton in
@[expose] def CFSG.KD.NRT.c17420.P : Prs := tri e17420 []

#kc_plan CFSG.KD.NRT.c17420 "c17420.plan.txt" 658 8824558211730722450
#kc_plan CFSG.KD.NRT.c17420 "c17420.grp.txt" 382 14540570581688507691
#kc_select CFSG.KD.NRT.c17420 CH CH 18
#kc_select CFSG.KD.NRT.c17420 PRf PR 18
#kc_select CFSG.KD.NRT.c17420 GKf GK 18
#kc_listDispatch CFSG.KD.NRT.c17420 Gf G 3

namespace CFSG.KD.NRT.c17420

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c17420

#kc_each CFSG.KD.NRT.c17420.u 0 3

end
