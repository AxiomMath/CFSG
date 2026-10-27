module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17494 "c17494.plan.txt" 2219 2815557838889105914
#kc_plan CFSG.KD.M5B.c17494 "c17494.grp.txt" 1392 5400159749051353485
#kc_select CFSG.KD.M5B.c17494 CH CH 63
#kc_select CFSG.KD.M5B.c17494 PRf PR 54
#kc_select CFSG.KD.M5B.c17494 GKf GK 63
#kc_listDispatch CFSG.KD.M5B.c17494 Gf G 12

namespace CFSG.KD.M5B.c17494

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [1, 10] CH PRf Gf g

end CFSG.KD.M5B.c17494

#kc_each CFSG.KD.M5B.c17494.u 0 12

end
