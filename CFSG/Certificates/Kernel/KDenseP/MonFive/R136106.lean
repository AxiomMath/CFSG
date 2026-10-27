module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136106

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (relTail 68) []

end CFSG.KD.M5R.c136106

#kc_plan CFSG.KD.M5R.c136106 "c136106.plan.txt" 3313 5364698926274145932
#kc_plan CFSG.KD.M5R.c136106 "c136106.grp.txt" 1643 11508418837306466876
#kc_select CFSG.KD.M5R.c136106 CH CH 72
#kc_select CFSG.KD.M5R.c136106 IXf IX 84
#kc_select CFSG.KD.M5R.c136106 PRf PR 63
#kc_select CFSG.KD.M5R.c136106 GKf GK 72
#kc_listDispatch CFSG.KD.M5R.c136106 Gf G 12

namespace CFSG.KD.M5R.c136106

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136106

#kc_each CFSG.KD.M5R.c136106.u 0 12

end
