module

public import CFSG.Certificates.Kernel.KDenseP.M13.Run
public import CFSG.Certificates.Kernel.KDenseP.M13.Pairs16957
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M13.c16957 "c16957.plan.txt" 8432 1285142312630207987
#kc_plan CFSG.KD.M13.c16957 "c16957.grp.txt" 4645 12575090400513852406
#kc_select CFSG.KD.M13.c16957 CH CH 216
#kc_select CFSG.KD.M13.c16957 PRf PR 147
#kc_select CFSG.KD.M13.c16957 GKf GK 216
#kc_listDispatch CFSG.KD.M13.c16957 Gf G 24

namespace CFSG.KD.M13.c16957

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB CFSG.KC.KDenseP.M13

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri e16957 []) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e16957 [])) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M13.c16957

#kc_each CFSG.KD.M13.c16957.u 0 24

end
