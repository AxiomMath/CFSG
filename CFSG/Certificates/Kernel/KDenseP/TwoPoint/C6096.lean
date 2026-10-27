module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoTab
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Pairs
public import Certificates.Data.Kernel.KDenseP.Words
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import CFSG.Monster.AxisCount.CoverLetters
public import CFSG.Monster.B.TwoA.Base.Flags
public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Monster.B.TwoA.Par3.MainBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionHom
public import CFSG.Monster.Existence.ELevelBasic
public import CFSG.Monster.Existence.TwoPoint.Fi23ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23MiscBase
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels0Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels1Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels2Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels3Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels4Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels5Base
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongADBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongMBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongPBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CommBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23S4CubeBase
public import CFSG.Monster.Existence.TwoPoint.GammaExclCheckBase
public import CFSG.Monster.Existence.TwoPoint.ThetaTrace
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.Sporadic.Co1Base
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.TP.c6096 "c6096.plan.txt" 36746 7032655589000980900
#kc_plan CFSG.KD.TP.c6096 "c6096.grp.txt" 1063 5767163740467878518
#kc_select CFSG.KD.TP.c6096 CH CH 48
#kc_select CFSG.KD.TP.c6096 IXf IX 48
#kc_select CFSG.KD.TP.c6096 PRf PR 45
#kc_select CFSG.KD.TP.c6096 GKf GK 48
#kc_listDispatch CFSG.KD.TP.c6096 WD wd 6
#kc_listDispatch CFSG.KD.TP.c6096 Gf G 6

namespace CFSG.KD.TP.c6096

open CFSG.KC.KDense

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen :=
  CFSG.KC.KDenseP.decW (WD σ)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := CFSG.KD.TP.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

end CFSG.KD.TP.c6096

end
