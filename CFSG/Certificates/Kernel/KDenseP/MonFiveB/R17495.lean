module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17495 "c17495.plan.txt" 1971 7033142588439018336
#kc_plan CFSG.KD.M5B.c17495 "c17495.grp.txt" 1261 5172292141165920732
#kc_select CFSG.KD.M5B.c17495 CH CH 57
#kc_select CFSG.KD.M5B.c17495 PRf PR 51
#kc_select CFSG.KD.M5B.c17495 GKf GK 57
#kc_listDispatch CFSG.KD.M5B.c17495 Gf G 9

namespace CFSG.KD.M5B.c17495

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [2, 9] CH PRf Gf g

end CFSG.KD.M5B.c17495

#kc_each CFSG.KD.M5B.c17495.u 0 9

end
