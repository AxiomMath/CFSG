module

public import CFSG.Certificates.Kernel.KDenseP.MonThreeB.Run
public import Certificates.Data.Kernel.KDenseP.Replay
public import CFSG.Certificates.Kernel.Common.Plan
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.YGroups.Y443.Native.EdgeNoncomm

public section

set_option maxRecDepth 100000

#kc_plan CFSG.KD.M3B.c13638 "c13638.plan.txt" 5110 3117256036194304254
#kc_plan CFSG.KD.M3B.c13638 "c13638.grp.txt" 3878 2637702437674738996
#kc_repo #kc_ktree CFSG.KD.M3B.c13638 RT "CFSG/Certificates/Kernel/KDenseP/MonThreeB/c13638.rec.bin" 129721 4
  14917915 11746211489923918254
#kc_select CFSG.KD.M3B.c13638 CH CH 144
#kc_select CFSG.KD.M3B.c13638 PRf PR 118
#kc_select CFSG.KD.M3B.c13638 GKf GK 144
#kc_listDispatch CFSG.KD.M3B.c13638 Gf G 101

namespace CFSG.KD.M3B.c13638

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] noncomputable def RXf (j : Nat) : Nat :=
  Nat.land (RT j) (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 509656)) (nat_lit 1))

@[expose] noncomputable def RAf (j : Nat) : Nat :=
  Nat.land (Nat.shiftRight (RT j) (nat_lit 509656))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3832)) (nat_lit 1))

@[expose] noncomputable def RWf (j : Nat) : Nat := Nat.shiftRight (RT j) (nat_lit 513488)

@[expose] noncomputable def S0 (k : Nat) : St :=
  Bool.rec (motive := fun _ => St) ((fun j => mkSt (RXf j) (RAf j) (RWf j)) (Nat.sub k 3))
    (CFSG.KD.KDF.I k) (Nat.blt k 3)

theorem S0_lt {k : Nat} (h : k < 3) : S0 k = CFSG.KD.KDF.I k := by
  have e : Nat.blt k 3 = true := by rw [Nat.blt_eq]; exact h
  unfold S0
  rw [e]

@[expose] noncomputable def rn (c : Nat) (s : St) : St :=
  runP (tri m7APairs n13638) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri m7APairs n13638)) CH PRf Gf S0 (nat_lit 118) g

end CFSG.KD.M3B.c13638

#kc_each CFSG.KD.M3B.c13638.u 0 101

end
