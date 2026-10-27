module

public import CFSG.Certificates.Kernel.KDenseP.MonFive.Rp
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CFSG.KD.M5R.c136105

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.KC.KDenseP.MonFive

@[expose] def P : List (List CFSG.Monster.AxisCount.Native.Gen × List CFSG.Monster.AxisCount.Native.Gen) :=
  tri3 (relSeg 57 11) []

end CFSG.KD.M5R.c136105

#kc_plan CFSG.KD.M5R.c136105 "c136105.plan.txt" 9413 3814628698226237004
#kc_plan CFSG.KD.M5R.c136105 "c136105.grp.txt" 4846 10054142585255684013
#kc_select CFSG.KD.M5R.c136105 CH CH 195
#kc_select CFSG.KD.M5R.c136105 IXf IX 249
#kc_select CFSG.KD.M5R.c136105 PRf PR 165
#kc_select CFSG.KD.M5R.c136105 GKf GK 195
#kc_listDispatch CFSG.KD.M5R.c136105 Gf G 33

namespace CFSG.KD.M5R.c136105

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def u (g : Nat) : Bool := CFSG.KD.M5RL.grpRL P CH PRf Gf g

end CFSG.KD.M5R.c136105

#kc_each CFSG.KD.M5R.c136105.u 0 33

end
