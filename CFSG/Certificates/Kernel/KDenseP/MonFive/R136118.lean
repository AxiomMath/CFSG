module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136118

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 15 3) (nesOf 15 3)

end CFSG.KD.M5R.c136118

#kc_plan CFSG.KD.M5R.c136118 "c136118.plan.txt" 17084 43291991816409637
#kc_plan CFSG.KD.M5R.c136118 "c136118.grp.txt" 8894 2973823694513663971
#kc_select CFSG.KD.M5R.c136118 CH CH 354
#kc_select CFSG.KD.M5R.c136118 IXf IX 390
#kc_select CFSG.KD.M5R.c136118 PRf PR 282
#kc_select CFSG.KD.M5R.c136118 GKf GK 354
#kc_listDispatch CFSG.KD.M5R.c136118 Gf G 64

namespace CFSG.KD.M5R.c136118

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136118

#kc_each CFSG.KD.M5R.c136118.u 0 64

end
