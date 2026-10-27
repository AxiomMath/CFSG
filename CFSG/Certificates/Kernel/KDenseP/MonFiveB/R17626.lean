module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17626 "c17626.plan.txt" 1446 6688024649723253264
#kc_plan CFSG.KD.M5B.c17626 "c17626.grp.txt" 925 13616291912565689211
#kc_select CFSG.KD.M5B.c17626 CH CH 42
#kc_select CFSG.KD.M5B.c17626 PRf PR 39
#kc_select CFSG.KD.M5B.c17626 GKf GK 42
#kc_listDispatch CFSG.KD.M5B.c17626 Gf G 6

namespace CFSG.KD.M5B.c17626

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [30] CH PRf Gf g

end CFSG.KD.M5B.c17626

#kc_each CFSG.KD.M5B.c17626.u 0 6

end
