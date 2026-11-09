module

public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.MonoTab
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Pairs
public import Certificates.Data.Kernel.KDenseP.Words
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.KDenseP.TwoPoint.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
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

#kc_plan CFSG.KD.TP.c6094 "c6094.plan.txt" 26962 13565509910727158787
#kc_plan CFSG.KD.TP.c6094 "c6094.grp.txt" 1002 6761839014272373127
#kc_repo #kc_ktree CFSG.KD.TP.c6094 RT "CFSG/Certificates/Kernel/KDenseP/TwoPoint/c6094.rec.bin" 129721 4
  3891630 9967493919850782839
#kc_select CFSG.KD.TP.c6094 CH CH 36
#kc_select CFSG.KD.TP.c6094 IXf IX 36
#kc_select CFSG.KD.TP.c6094 PRf PR 33
#kc_select CFSG.KD.TP.c6094 GKf GK 36
#kc_listDispatch CFSG.KD.TP.c6094 WD wd 6
#kc_listDispatch CFSG.KD.TP.c6094 Gf G 33

namespace CFSG.KD.TP.c6094

open CFSG.KC.KDense

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen :=
  CFSG.KC.KDenseP.decW (WD σ)

@[expose] noncomputable def RXf (j : Nat) : Nat :=
  Nat.land (RT j) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 509656)) (nat_lit 1))

@[expose] noncomputable def RAf (j : Nat) : Nat :=
  Nat.land (Nat.shiftRight (RT j) (nat_lit 509656)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3832)) (nat_lit 1))

@[expose] noncomputable def RWf (j : Nat) : Nat := Nat.shiftRight (RT j) (nat_lit 513488)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

@[expose] noncomputable def rn (c : Nat) (s : St) : St := CFSG.KD.TP.run (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

end CFSG.KD.TP.c6094

end
