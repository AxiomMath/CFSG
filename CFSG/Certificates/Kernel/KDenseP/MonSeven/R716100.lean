module

public import CFSG.Certificates.Kernel.KDenseP.MonSeven.Look
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M7.c716100

open CFSG.KC.KDenseP.MonSeven

@[expose] noncomputable def P : Prs :=
  tri CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenFlag.m7hPairs []

end CFSG.KD.M7.c716100

#kc_plan CFSG.KD.M7.c716100 "c716100.plan.txt" 6027 11941440303283424115
#kc_plan CFSG.KD.M7.c716100 "c716100.grp.txt" 3124 4740030907275533421
#kc_select CFSG.KD.M7.c716100 CH CH 132
#kc_select CFSG.KD.M7.c716100 IXf IX 159
#kc_select CFSG.KD.M7.c716100 PRf PR 120
#kc_select CFSG.KD.M7.c716100 GKf GK 132
#kc_listDispatch CFSG.KD.M7.c716100 Gf G 15

namespace CFSG.KD.M7.c716100

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M7L.grpRP P CH PRf Gf g

end CFSG.KD.M7.c716100

#kc_each CFSG.KD.M7.c716100.u 0 15

end
