module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136117

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (repEqsOf 12 3) (nesOf 12 3)

end CFSG.KD.M5R.c136117

#kc_plan CFSG.KD.M5R.c136117 "c136117.plan.txt" 16494 9427735464286419432
#kc_plan CFSG.KD.M5R.c136117 "c136117.grp.txt" 8501 2647656512760127860
#kc_select CFSG.KD.M5R.c136117 CH CH 340
#kc_select CFSG.KD.M5R.c136117 IXf IX 379
#kc_select CFSG.KD.M5R.c136117 PRf PR 268
#kc_select CFSG.KD.M5R.c136117 GKf GK 340
#kc_listDispatch CFSG.KD.M5R.c136117 Gf G 62

namespace CFSG.KD.M5R.c136117

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136117

#kc_each CFSG.KD.M5R.c136117.u 0 62

end
