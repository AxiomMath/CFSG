module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Look
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2T3Words
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M7.c17473

open CFSG.KC.KDenseP.MonSeven

@[expose] noncomputable def P : Prs := tri CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bT3Eqs []

end CFSG.KD.M7.c17473

#kc_plan CFSG.KD.M7.c17473 "c17473.plan.txt" 5505 17322570598846521617
#kc_plan CFSG.KD.M7.c17473 "c17473.grp.txt" 2715 6438477742874222225
#kc_select CFSG.KD.M7.c17473 CH CH 120
#kc_select CFSG.KD.M7.c17473 IXf IX 126
#kc_select CFSG.KD.M7.c17473 PRf PR 99
#kc_select CFSG.KD.M7.c17473 GKf GK 120
#kc_listDispatch CFSG.KD.M7.c17473 Gf G 21

namespace CFSG.KD.M7.c17473

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M7L.grpRP P CH PRf Gf g

end CFSG.KD.M7.c17473

#kc_each CFSG.KD.M7.c17473.u 0 21

end
