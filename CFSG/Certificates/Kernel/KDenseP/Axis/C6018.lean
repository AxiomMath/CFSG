module

public import CFSG.Certificates.Kernel.KDenseP.Axis.MonoTab
public import CFSG.Certificates.Kernel.KDenseP.Axis.Pairs
public import Certificates.Data.Kernel.KDenseP.Words
public import Certificates.Data.Kernel.KDenseP.Val
public import CFSG.Certificates.Kernel.KDense.Data.Fix
public import CFSG.Certificates.Kernel.KDenseP.Axis.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.AX.c6018 "c6018.plan.txt" 240534 7144311631700951936
#kc_plan CFSG.KD.AX.c6018 "c6018.grp.txt" 3280 18260743198698702913
#kc_repo #kc_ktree CFSG.KD.AX.c6018 RT "CFSG/Certificates/Kernel/KDenseP/Axis/c6018.rec.bin" 96825 4
  5034900 757816383482989233
#kc_select CFSG.KD.AX.c6018 CH CH 151
#kc_select CFSG.KD.AX.c6018 IXf IX 210
#kc_select CFSG.KD.AX.c6018 PRf PR 55
#kc_select CFSG.KD.AX.c6018 GKf GK 151
#kc_listDispatch CFSG.KD.AX.c6018 WD wd 144
#kc_listDispatch CFSG.KD.AX.c6018 Gf G 88

namespace CFSG.KD.AX.c6018

open CFSG.KC.KDense CFSG.KC.KDenseP

@[expose] noncomputable def WL (σ : Nat) : List CFSG.Monster.AxisCount.Native.Gen :=
  CFSG.KC.KDenseP.decW (WD σ)

@[expose] noncomputable def RXf (j : Nat) : Nat :=
  Nat.land (RT j) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 378584)) (nat_lit 1))

@[expose] noncomputable def RAf (j : Nat) : Nat :=
  Nat.land (Nat.shiftRight (RT j) (nat_lit 378584)) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 2808)) (nat_lit 1))

@[expose] noncomputable def RWf (j : Nat) : Nat := Nat.shiftRight (RT j) (nat_lit 381392)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (Bool.rec (motive := fun _ => St) (Bool.rec (motive := fun _ => St) (mkSt I0X I0A I0W)
      (mkSt I1X I1A I1W) (Nat.beq k 1)) (mkSt I0X I0A I0W) (Nat.beq k 0)) (Nat.blt k 3)

@[expose] noncomputable def CHI (k : Nat) : Nat := CH (IXf k)

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  CFSG.KD.AX.run3 (WD (f20 c (nat_lit 0))) c s

@[expose] noncomputable def ck (S : Nat → St) (c : Nat) : Bool :=
  chunkOKN (nat_lit 3) (nat_lit 2) (nat_lit 7) CFSG.KD.KDF.F CFSG.KD.AXM.MT WL S c

@[expose] noncomputable def u (g : Nat) : Bool := grpL rn ck CH PRf Gf S0 (nat_lit 55) g

end CFSG.KD.AX.c6018

end
