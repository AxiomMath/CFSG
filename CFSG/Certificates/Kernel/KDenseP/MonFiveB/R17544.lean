module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17544 "c17544.plan.txt" 1971 7303628698196990968
#kc_plan CFSG.KD.M5B.c17544 "c17544.grp.txt" 1261 13268824879653309280
#kc_select CFSG.KD.M5B.c17544 CH CH 57
#kc_select CFSG.KD.M5B.c17544 PRf PR 51
#kc_select CFSG.KD.M5B.c17544 GKf GK 57
#kc_listDispatch CFSG.KD.M5B.c17544 Gf G 9

namespace CFSG.KD.M5B.c17544

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [7, 23] CH PRf Gf g

end CFSG.KD.M5B.c17544

#kc_each CFSG.KD.M5B.c17544.u 0 9

end
