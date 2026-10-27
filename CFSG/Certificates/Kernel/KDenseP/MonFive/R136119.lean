module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136119

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 18 2) (nesOf 18 2)

end CFSG.KD.M5R.c136119

#kc_plan CFSG.KD.M5R.c136119 "c136119.plan.txt" 11750 17688050752305711504
#kc_plan CFSG.KD.M5R.c136119 "c136119.grp.txt" 6008 12879869208585136931
#kc_select CFSG.KD.M5R.c136119 CH CH 247
#kc_select CFSG.KD.M5R.c136119 IXf IX 277
#kc_select CFSG.KD.M5R.c136119 PRf PR 200
#kc_select CFSG.KD.M5R.c136119 GKf GK 247
#kc_listDispatch CFSG.KD.M5R.c136119 Gf G 43

namespace CFSG.KD.M5R.c136119

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136119

#kc_each CFSG.KD.M5R.c136119.u 0 43

end
