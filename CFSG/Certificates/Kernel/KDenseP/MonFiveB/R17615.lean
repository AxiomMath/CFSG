module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17615 "c17615.plan.txt" 1725 12275096388559985552
#kc_plan CFSG.KD.M5B.c17615 "c17615.grp.txt" 1131 12758734098774364834
#kc_select CFSG.KD.M5B.c17615 CH CH 51
#kc_select CFSG.KD.M5B.c17615 PRf PR 48
#kc_select CFSG.KD.M5B.c17615 GKf GK 51
#kc_listDispatch CFSG.KD.M5B.c17615 Gf G 6

namespace CFSG.KD.M5B.c17615

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [16, 26] CH PRf Gf g

end CFSG.KD.M5B.c17615

#kc_each CFSG.KD.M5B.c17615.u 0 6

end
