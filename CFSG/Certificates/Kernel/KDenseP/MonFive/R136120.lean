module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136120

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 20 2) (nesOf 20 2)

end CFSG.KD.M5R.c136120

#kc_plan CFSG.KD.M5R.c136120 "c136120.plan.txt" 11907 16342885515371844709
#kc_plan CFSG.KD.M5R.c136120 "c136120.grp.txt" 6064 4975770679170921199
#kc_select CFSG.KD.M5R.c136120 CH CH 250
#kc_select CFSG.KD.M5R.c136120 IXf IX 283
#kc_select CFSG.KD.M5R.c136120 PRf PR 203
#kc_select CFSG.KD.M5R.c136120 GKf GK 250
#kc_listDispatch CFSG.KD.M5R.c136120 Gf G 40

namespace CFSG.KD.M5R.c136120

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136120

#kc_each CFSG.KD.M5R.c136120.u 0 40

end
