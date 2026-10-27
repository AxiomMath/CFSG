module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c13699

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (relSeg 0 13) []

end CFSG.KD.M5R.c13699

#kc_plan CFSG.KD.M5R.c13699 "c13699.plan.txt" 10268 2905713685315178307
#kc_plan CFSG.KD.M5R.c13699 "c13699.grp.txt" 5263 12008097515571476165
#kc_select CFSG.KD.M5R.c13699 CH CH 210
#kc_select CFSG.KD.M5R.c13699 IXf IX 270
#kc_select CFSG.KD.M5R.c13699 PRf PR 174
#kc_select CFSG.KD.M5R.c13699 GKf GK 210
#kc_listDispatch CFSG.KD.M5R.c13699 Gf G 39

namespace CFSG.KD.M5R.c13699

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c13699

#kc_each CFSG.KD.M5R.c13699.u 0 39

end
