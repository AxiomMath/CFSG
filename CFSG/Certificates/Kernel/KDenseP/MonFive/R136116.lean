module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136116

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 9 3) (nesOf 9 3)

end CFSG.KD.M5R.c136116

#kc_plan CFSG.KD.M5R.c136116 "c136116.plan.txt" 17715 5622298628177269392
#kc_plan CFSG.KD.M5R.c136116 "c136116.grp.txt" 9207 6953814114857047927
#kc_select CFSG.KD.M5R.c136116 CH CH 363
#kc_select CFSG.KD.M5R.c136116 IXf IX 420
#kc_select CFSG.KD.M5R.c136116 PRf PR 291
#kc_select CFSG.KD.M5R.c136116 GKf GK 363
#kc_listDispatch CFSG.KD.M5R.c136116 Gf G 62

namespace CFSG.KD.M5R.c136116

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136116

#kc_each CFSG.KD.M5R.c136116.u 0 62

end
