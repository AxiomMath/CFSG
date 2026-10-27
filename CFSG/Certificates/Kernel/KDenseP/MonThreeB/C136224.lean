module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M3B.c136224 "c136224.plan.txt" 352 15962060745874338196
#kc_plan CFSG.KD.M3B.c136224 "c136224.grp.txt" 167 1815952228835067238
#kc_select CFSG.KD.M3B.c136224 CH CH 8
#kc_select CFSG.KD.M3B.c136224 PRf PR 9
#kc_select CFSG.KD.M3B.c136224 GKf GK 8
#kc_listDispatch CFSG.KD.M3B.c136224 Gf G 1

namespace CFSG.KD.M3B.c136224

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri [] n136224) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri [] n136224)) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M3B.c136224

#kc_each CFSG.KD.M3B.c136224.u 0 1

end
