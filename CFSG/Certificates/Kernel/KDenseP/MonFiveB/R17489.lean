module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17489 "c17489.plan.txt" 1791 7452929721522201399
#kc_plan CFSG.KD.M5B.c17489 "c17489.grp.txt" 1109 12569855831702069769
#kc_select CFSG.KD.M5B.c17489 CH CH 51
#kc_select CFSG.KD.M5B.c17489 PRf PR 45
#kc_select CFSG.KD.M5B.c17489 GKf GK 51
#kc_listDispatch CFSG.KD.M5B.c17489 Gf G 7

namespace CFSG.KD.M5B.c17489

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [0, 14] CH PRf Gf g

end CFSG.KD.M5B.c17489

#kc_each CFSG.KD.M5B.c17489.u 0 7

end
