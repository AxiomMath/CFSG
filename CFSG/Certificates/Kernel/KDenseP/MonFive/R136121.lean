module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136121

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 22 3) (nesOf 22 3)

end CFSG.KD.M5R.c136121

#kc_plan CFSG.KD.M5R.c136121 "c136121.plan.txt" 18166 9627036088744141646
#kc_plan CFSG.KD.M5R.c136121 "c136121.grp.txt" 9562 1791661688698459044
#kc_select CFSG.KD.M5R.c136121 CH CH 377
#kc_select CFSG.KD.M5R.c136121 IXf IX 419
#kc_select CFSG.KD.M5R.c136121 PRf PR 305
#kc_select CFSG.KD.M5R.c136121 GKf GK 377
#kc_listDispatch CFSG.KD.M5R.c136121 Gf G 65

namespace CFSG.KD.M5R.c136121

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136121

#kc_each CFSG.KD.M5R.c136121.u 0 65

end
