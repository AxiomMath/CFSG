module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M3B.c136220 "c136220.plan.txt" 6944 14304639427447999029
#kc_plan CFSG.KD.M3B.c136220 "c136220.grp.txt" 4904 4833520065520141003
#kc_select CFSG.KD.M3B.c136220 CH CH 207
#kc_select CFSG.KD.M3B.c136220 PRf PR 186
#kc_select CFSG.KD.M3B.c136220 GKf GK 207
#kc_listDispatch CFSG.KD.M3B.c136220 Gf G 21

namespace CFSG.KD.M3B.c136220

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri e136220 []) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e136220 [])) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M3B.c136220

#kc_each CFSG.KD.M3B.c136220.u 0 21

end
