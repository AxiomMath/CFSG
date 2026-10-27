module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136101

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (relSeg 25 10) []

end CFSG.KD.M5R.c136101

#kc_plan CFSG.KD.M5R.c136101 "c136101.plan.txt" 9560 5854367517359364260
#kc_plan CFSG.KD.M5R.c136101 "c136101.grp.txt" 5138 10587200391706426706
#kc_select CFSG.KD.M5R.c136101 CH CH 213
#kc_select CFSG.KD.M5R.c136101 IXf IX 222
#kc_select CFSG.KD.M5R.c136101 PRf PR 186
#kc_select CFSG.KD.M5R.c136101 GKf GK 213
#kc_listDispatch CFSG.KD.M5R.c136101 Gf G 30

namespace CFSG.KD.M5R.c136101

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136101

#kc_each CFSG.KD.M5R.c136101.u 0 30

end
