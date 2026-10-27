module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136123

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 28 3) (nesOf 28 3)

end CFSG.KD.M5R.c136123

#kc_plan CFSG.KD.M5R.c136123 "c136123.plan.txt" 18146 14575416859730734300
#kc_plan CFSG.KD.M5R.c136123 "c136123.grp.txt" 9540 4514900452463576802
#kc_select CFSG.KD.M5R.c136123 CH CH 378
#kc_select CFSG.KD.M5R.c136123 IXf IX 414
#kc_select CFSG.KD.M5R.c136123 PRf PR 306
#kc_select CFSG.KD.M5R.c136123 GKf GK 378
#kc_listDispatch CFSG.KD.M5R.c136123 Gf G 62

namespace CFSG.KD.M5R.c136123

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136123

#kc_each CFSG.KD.M5R.c136123.u 0 62

end
