module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136100

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (relSeg 13 12) []

end CFSG.KD.M5R.c136100

#kc_plan CFSG.KD.M5R.c136100 "c136100.plan.txt" 9620 965875791074606305
#kc_plan CFSG.KD.M5R.c136100 "c136100.grp.txt" 4930 4191556435294862231
#kc_select CFSG.KD.M5R.c136100 CH CH 198
#kc_select CFSG.KD.M5R.c136100 IXf IX 252
#kc_select CFSG.KD.M5R.c136100 PRf PR 165
#kc_select CFSG.KD.M5R.c136100 GKf GK 198
#kc_listDispatch CFSG.KD.M5R.c136100 Gf G 36

namespace CFSG.KD.M5R.c136100

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136100

#kc_each CFSG.KD.M5R.c136100.u 0 36

end
