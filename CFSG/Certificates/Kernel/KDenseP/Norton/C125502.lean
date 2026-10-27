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
@[expose] def CFSG.KD.NRT.c125502.P : Prs := tri e125502 n125502

#kc_plan CFSG.KD.NRT.c125502 "c125502.plan.txt" 4201 12888427059241802745
#kc_plan CFSG.KD.NRT.c125502 "c125502.grp.txt" 2699 12728828744557114945
#kc_select CFSG.KD.NRT.c125502 CH CH 120
#kc_select CFSG.KD.NRT.c125502 PRf PR 101
#kc_select CFSG.KD.NRT.c125502 GKf GK 120
#kc_listDispatch CFSG.KD.NRT.c125502 Gf G 19

namespace CFSG.KD.NRT.c125502

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def rn (c : Nat) (s : St) : St := runP P (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP P) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.NRT.c125502

#kc_each CFSG.KD.NRT.c125502.u 0 19

end
