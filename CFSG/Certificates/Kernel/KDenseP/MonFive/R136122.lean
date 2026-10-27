module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136122

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 25 3) (nesOf 25 3)

end CFSG.KD.M5R.c136122

#kc_plan CFSG.KD.M5R.c136122 "c136122.plan.txt" 17340 5770655747541085786
#kc_plan CFSG.KD.M5R.c136122 "c136122.grp.txt" 9003 13919071221011478590
#kc_select CFSG.KD.M5R.c136122 CH CH 356
#kc_select CFSG.KD.M5R.c136122 IXf IX 407
#kc_select CFSG.KD.M5R.c136122 PRf PR 284
#kc_select CFSG.KD.M5R.c136122 GKf GK 356
#kc_listDispatch CFSG.KD.M5R.c136122 Gf G 65

namespace CFSG.KD.M5R.c136122

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136122

#kc_each CFSG.KD.M5R.c136122.u 0 65

end
