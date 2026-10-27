module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136113

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 0 3) (nesOf 0 3)

end CFSG.KD.M5R.c136113

#kc_plan CFSG.KD.M5R.c136113 "c136113.plan.txt" 16852 1580804990710770993
#kc_plan CFSG.KD.M5R.c136113 "c136113.grp.txt" 8618 2349902873406566240
#kc_select CFSG.KD.M5R.c136113 CH CH 342
#kc_select CFSG.KD.M5R.c136113 IXf IX 405
#kc_select CFSG.KD.M5R.c136113 PRf PR 270
#kc_select CFSG.KD.M5R.c136113 GKf GK 342
#kc_listDispatch CFSG.KD.M5R.c136113 Gf G 62

namespace CFSG.KD.M5R.c136113

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136113

#kc_each CFSG.KD.M5R.c136113.u 0 62

end
