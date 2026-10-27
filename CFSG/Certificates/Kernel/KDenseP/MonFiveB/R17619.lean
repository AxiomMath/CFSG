module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17619 "c17619.plan.txt" 1446 1565087108666100894
#kc_plan CFSG.KD.M5B.c17619 "c17619.grp.txt" 925 13616291912565689211
#kc_select CFSG.KD.M5B.c17619 CH CH 42
#kc_select CFSG.KD.M5B.c17619 PRf PR 39
#kc_select CFSG.KD.M5B.c17619 GKf GK 42
#kc_listDispatch CFSG.KD.M5B.c17619 Gf G 6

namespace CFSG.KD.M5B.c17619

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [24] CH PRf Gf g

end CFSG.KD.M5B.c17619

#kc_each CFSG.KD.M5B.c17619.u 0 6

end
