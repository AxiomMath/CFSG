module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136111

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (normTail 23) []

end CFSG.KD.M5R.c136111

#kc_plan CFSG.KD.M5R.c136111 "c136111.plan.txt" 5287 13569293858049886461
#kc_plan CFSG.KD.M5R.c136111 "c136111.grp.txt" 2777 4690760953580884313
#kc_select CFSG.KD.M5R.c136111 CH CH 120
#kc_select CFSG.KD.M5R.c136111 IXf IX 132
#kc_select CFSG.KD.M5R.c136111 PRf PR 111
#kc_select CFSG.KD.M5R.c136111 GKf GK 120
#kc_listDispatch CFSG.KD.M5R.c136111 Gf G 12

namespace CFSG.KD.M5R.c136111

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136111

#kc_each CFSG.KD.M5R.c136111.u 0 12

end
