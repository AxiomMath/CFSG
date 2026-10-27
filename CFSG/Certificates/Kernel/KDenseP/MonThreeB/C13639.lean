module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M3B.c13639 "c13639.plan.txt" 5926 9496912062611767145
#kc_plan CFSG.KD.M3B.c13639 "c13639.grp.txt" 3794 12436785018935159430
#kc_select CFSG.KD.M3B.c13639 CH CH 167
#kc_select CFSG.KD.M3B.c13639 PRf PR 136
#kc_select CFSG.KD.M3B.c13639 GKf GK 167
#kc_listDispatch CFSG.KD.M3B.c13639 Gf G 22

namespace CFSG.KD.M3B.c13639

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri m7BPairs n13639) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri m7BPairs n13639)) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M3B.c13639

#kc_each CFSG.KD.M3B.c13639.u 0 22

end
