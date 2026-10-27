module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136112

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 [] [(fiveGens[8]!, [])]

end CFSG.KD.M5R.c136112

#kc_plan CFSG.KD.M5R.c136112 "c136112.plan.txt" 207 7471355847998568498
#kc_plan CFSG.KD.M5R.c136112 "c136112.grp.txt" 80 5085449357414359540
#kc_select CFSG.KD.M5R.c136112 CH CH 3
#kc_select CFSG.KD.M5R.c136112 IXf IX 3
#kc_select CFSG.KD.M5R.c136112 PRf PR 5
#kc_select CFSG.KD.M5R.c136112 GKf GK 3
#kc_listDispatch CFSG.KD.M5R.c136112 Gf G 1

namespace CFSG.KD.M5R.c136112

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136112

#kc_each CFSG.KD.M5R.c136112.u 0 1

end
