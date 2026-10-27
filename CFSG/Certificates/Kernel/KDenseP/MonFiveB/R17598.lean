module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17598 "c17598.plan.txt" 1971 10936100884009585526
#kc_plan CFSG.KD.M5B.c17598 "c17598.grp.txt" 1261 9669870762911092180
#kc_select CFSG.KD.M5B.c17598 CH CH 57
#kc_select CFSG.KD.M5B.c17598 PRf PR 51
#kc_select CFSG.KD.M5B.c17598 GKf GK 57
#kc_listDispatch CFSG.KD.M5B.c17598 Gf G 9

namespace CFSG.KD.M5B.c17598

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [8, 11] CH PRf Gf g

end CFSG.KD.M5B.c17598

#kc_each CFSG.KD.M5B.c17598.u 0 9

end
