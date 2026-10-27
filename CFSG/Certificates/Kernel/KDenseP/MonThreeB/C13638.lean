module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M3B.c13638 "c13638.plan.txt" 5110 3117256036194304254
#kc_plan CFSG.KD.M3B.c13638 "c13638.grp.txt" 3261 13829927981378980065
#kc_select CFSG.KD.M3B.c13638 CH CH 144
#kc_select CFSG.KD.M3B.c13638 PRf PR 118
#kc_select CFSG.KD.M3B.c13638 GKf GK 144
#kc_listDispatch CFSG.KD.M3B.c13638 Gf G 22

namespace CFSG.KD.M3B.c13638

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri m7APairs n13638) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri m7APairs n13638)) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M3B.c13638

#kc_each CFSG.KD.M3B.c13638.u 0 22

end
