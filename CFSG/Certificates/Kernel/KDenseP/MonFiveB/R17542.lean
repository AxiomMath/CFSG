module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17542 "c17542.plan.txt" 1815 8546181370540228652
#kc_plan CFSG.KD.M5B.c17542 "c17542.grp.txt" 1200 11346198057429241503
#kc_select CFSG.KD.M5B.c17542 CH CH 54
#kc_select CFSG.KD.M5B.c17542 PRf PR 51
#kc_select CFSG.KD.M5B.c17542 GKf GK 54
#kc_listDispatch CFSG.KD.M5B.c17542 Gf G 6

namespace CFSG.KD.M5B.c17542

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [5, 29] CH PRf Gf g

end CFSG.KD.M5B.c17542

#kc_each CFSG.KD.M5B.c17542.u 0 6

end
