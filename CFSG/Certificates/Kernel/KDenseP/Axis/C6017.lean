module

public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoTab
public import CFSG.Certificates.Kernel.KDenseP.Axis.Pairs
public import Certificates.Data.Kernel.KDenseP.Words
public import Certificates.Data.Kernel.KDenseP.Val
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.KDenseP.Axis.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.AX.c6017 "c6017.plan.txt" 241039 5095417556659127773
#kc_plan CFSG.KD.AX.c6017 "c6017.grp.txt" 1893 15007761491276272092
#kc_select CFSG.KD.AX.c6017 CH CH 107
#kc_select CFSG.KD.AX.c6017 IXf IX 173
#kc_select CFSG.KD.AX.c6017 PRf PR 39
#kc_select CFSG.KD.AX.c6017 GKf GK 107
#kc_listDispatch CFSG.KD.AX.c6017 WD wd 96
#kc_listDispatch CFSG.KD.AX.c6017 Gf G 11

namespace CFSG.KD.AX.c6017

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen :=
  CFSG.KC.KDenseP.decW (WD σ)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) (Bool.rec (motive := fun _ => St) (mkSt I0X I0A I0W)
    (mkSt I1X I1A I1W) (Nat.beq k 1)) (mkSt I0X I0A I0W) (Nat.beq k 0)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.AX.run3 (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def ck (S : Nat → St) (c : Nat) : Bool :=
  chunkOKN (nat_lit 3) (nat_lit 2) (nat_lit 7) CFSG.KD.KDF.F CFSG.KD.AXM.MT WL S c

@[expose] noncomputable def u (g : Nat) : Bool := grpL rn ck CH PRf Gf S0 (nat_lit 3) g

end CFSG.KD.AX.c6017

end
