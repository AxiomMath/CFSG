module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136115

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 6 3) (nesOf 6 3)

end CFSG.KD.M5R.c136115

#kc_plan CFSG.KD.M5R.c136115 "c136115.plan.txt" 16776 11282801437543639381
#kc_plan CFSG.KD.M5R.c136115 "c136115.grp.txt" 8673 14350888370044069948
#kc_select CFSG.KD.M5R.c136115 CH CH 344
#kc_select CFSG.KD.M5R.c136115 IXf IX 392
#kc_select CFSG.KD.M5R.c136115 PRf PR 272
#kc_select CFSG.KD.M5R.c136115 GKf GK 344
#kc_listDispatch CFSG.KD.M5R.c136115 Gf G 64

namespace CFSG.KD.M5R.c136115

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136115

#kc_each CFSG.KD.M5R.c136115.u 0 64

end
