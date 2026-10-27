module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17614 "c17614.plan.txt" 1356 18399497609490611494
#kc_plan CFSG.KD.M5B.c17614 "c17614.grp.txt" 856 8259488987155426284
#kc_select CFSG.KD.M5B.c17614 CH CH 39
#kc_select CFSG.KD.M5B.c17614 PRf PR 36
#kc_select CFSG.KD.M5B.c17614 GKf GK 39
#kc_listDispatch CFSG.KD.M5B.c17614 Gf G 6

namespace CFSG.KD.M5B.c17614

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [13] CH PRf Gf g

end CFSG.KD.M5B.c17614

#kc_each CFSG.KD.M5B.c17614.u 0 6

end
