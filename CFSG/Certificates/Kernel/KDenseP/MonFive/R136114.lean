module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136114

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 3 3) (nesOf 3 3)

end CFSG.KD.M5R.c136114

#kc_plan CFSG.KD.M5R.c136114 "c136114.plan.txt" 17217 17621676869979688811
#kc_plan CFSG.KD.M5R.c136114 "c136114.grp.txt" 8896 17435595949101629122
#kc_select CFSG.KD.M5R.c136114 CH CH 354
#kc_select CFSG.KD.M5R.c136114 IXf IX 402
#kc_select CFSG.KD.M5R.c136114 PRf PR 282
#kc_select CFSG.KD.M5R.c136114 GKf GK 354
#kc_listDispatch CFSG.KD.M5R.c136114 Gf G 59

namespace CFSG.KD.M5R.c136114

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136114

#kc_each CFSG.KD.M5R.c136114.u 0 59

end
