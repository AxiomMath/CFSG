module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M3B.c136221 "c136221.plan.txt" 9327 12906655729232901777
#kc_plan CFSG.KD.M3B.c136221 "c136221.grp.txt" 6219 5506381956671927036
#kc_select CFSG.KD.M3B.c136221 CH CH 261
#kc_select CFSG.KD.M3B.c136221 PRf PR 210
#kc_select CFSG.KD.M3B.c136221 GKf GK 261
#kc_listDispatch CFSG.KD.M3B.c136221 Gf G 43

namespace CFSG.KD.M3B.c136221

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri e136221 []) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e136221 [])) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M3B.c136221

#kc_each CFSG.KD.M3B.c136221.u 0 43

end
