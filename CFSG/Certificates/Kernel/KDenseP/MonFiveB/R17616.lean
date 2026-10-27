module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17616 "c17616.plan.txt" 1815 472356596390758827
#kc_plan CFSG.KD.M5B.c17616 "c17616.grp.txt" 1200 6906666312569312739
#kc_select CFSG.KD.M5B.c17616 CH CH 54
#kc_select CFSG.KD.M5B.c17616 PRf PR 51
#kc_select CFSG.KD.M5B.c17616 GKf GK 54
#kc_listDispatch CFSG.KD.M5B.c17616 Gf G 6

namespace CFSG.KD.M5B.c17616

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [17, 22] CH PRf Gf g

end CFSG.KD.M5B.c17616

#kc_each CFSG.KD.M5B.c17616.u 0 6

end
