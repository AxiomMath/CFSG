module

public import CFSG.Certificates.Kernel.KDenseP.MonFiveB.Look
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M5B.c17617 "c17617.plan.txt" 1356 893886405197592402
#kc_plan CFSG.KD.M5B.c17617 "c17617.grp.txt" 856 13735038077466872943
#kc_select CFSG.KD.M5B.c17617 CH CH 39
#kc_select CFSG.KD.M5B.c17617 PRf PR 36
#kc_select CFSG.KD.M5B.c17617 GKf GK 39
#kc_listDispatch CFSG.KD.M5B.c17617 Gf G 6

namespace CFSG.KD.M5B.c17617

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5BL.grpRB [18] CH PRf Gf g

end CFSG.KD.M5B.c17617

#kc_each CFSG.KD.M5B.c17617.u 0 6

end
