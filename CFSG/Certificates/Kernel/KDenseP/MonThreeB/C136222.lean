module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M3B.c136222 "c136222.plan.txt" 8393 7567323551071492837
#kc_plan CFSG.KD.M3B.c136222 "c136222.grp.txt" 5509 1515701910698642320
#kc_select CFSG.KD.M3B.c136222 CH CH 234
#kc_select CFSG.KD.M3B.c136222 PRf PR 186
#kc_select CFSG.KD.M3B.c136222 GKf GK 234
#kc_listDispatch CFSG.KD.M3B.c136222 Gf G 39

namespace CFSG.KD.M3B.c136222

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri e136222 []) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e136222 [])) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M3B.c136222

#kc_each CFSG.KD.M3B.c136222.u 0 39

end
