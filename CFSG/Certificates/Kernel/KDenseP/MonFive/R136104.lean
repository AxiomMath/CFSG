module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136104

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (relSeg 47 10) []

end CFSG.KD.M5R.c136104

#kc_plan CFSG.KD.M5R.c136104 "c136104.plan.txt" 9686 1938117927269063217
#kc_plan CFSG.KD.M5R.c136104 "c136104.grp.txt" 5093 9925863816823245566
#kc_select CFSG.KD.M5R.c136104 CH CH 207
#kc_select CFSG.KD.M5R.c136104 IXf IX 246
#kc_select CFSG.KD.M5R.c136104 PRf PR 180
#kc_select CFSG.KD.M5R.c136104 GKf GK 207
#kc_listDispatch CFSG.KD.M5R.c136104 Gf G 30

namespace CFSG.KD.M5R.c136104

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136104

#kc_each CFSG.KD.M5R.c136104.u 0 30

end
