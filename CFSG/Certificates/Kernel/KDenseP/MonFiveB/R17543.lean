module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17543 "c17543.plan.txt" 1815 4003971541296400367
#kc_plan CFSG.KD.M5B.c17543 "c17543.grp.txt" 1200 11346198057429241503
#kc_select CFSG.KD.M5B.c17543 CH CH 54
#kc_select CFSG.KD.M5B.c17543 PRf PR 51
#kc_select CFSG.KD.M5B.c17543 GKf GK 54
#kc_listDispatch CFSG.KD.M5B.c17543 Gf G 6

namespace CFSG.KD.M5B.c17543

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [6, 20] CH PRf Gf g

end CFSG.KD.M5B.c17543

#kc_each CFSG.KD.M5B.c17543.u 0 6

end
