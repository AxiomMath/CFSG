module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17625 "c17625.plan.txt" 1972 8669388554793101975
#kc_plan CFSG.KD.M5B.c17625 "c17625.grp.txt" 1261 10669164063948904380
#kc_select CFSG.KD.M5B.c17625 CH CH 57
#kc_select CFSG.KD.M5B.c17625 PRf PR 51
#kc_select CFSG.KD.M5B.c17625 GKf GK 57
#kc_listDispatch CFSG.KD.M5B.c17625 Gf G 9

namespace CFSG.KD.M5B.c17625

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [27, 28] CH PRf Gf g

end CFSG.KD.M5B.c17625

#kc_each CFSG.KD.M5B.c17625.u 0 9

end
