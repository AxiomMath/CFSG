module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M3B.c136223 "c136223.plan.txt" 7244 14519493288553749867
#kc_plan CFSG.KD.M3B.c136223 "c136223.grp.txt" 4954 18057650612503089763
#kc_select CFSG.KD.M3B.c136223 CH CH 207
#kc_select CFSG.KD.M3B.c136223 PRf PR 174
#kc_select CFSG.KD.M3B.c136223 GKf GK 207
#kc_listDispatch CFSG.KD.M3B.c136223 Gf G 36

namespace CFSG.KD.M3B.c136223

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri e136223 []) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e136223 [])) CH PRf Gf CFSG.KD.KDF.I (nat_lit 3) g

end CFSG.KD.M3B.c136223

#kc_each CFSG.KD.M3B.c136223.u 0 36

end
