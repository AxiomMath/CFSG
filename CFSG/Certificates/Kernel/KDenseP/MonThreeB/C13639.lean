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

#kc_plan CFSG.KD.M3B.c13639 "c13639.plan.txt" 5926 9496912062611767145
#kc_plan CFSG.KD.M3B.c13639 "c13639.grp.txt" 4666 17594201096159814091
#kc_repo #kc_ktree CFSG.KD.M3B.c13639 RT "CFSG/Certificates/Kernel/KDenseP/MonThreeB/c13639.rec.bin" 129721 4
  17252893 4795472571009555238
#kc_select CFSG.KD.M3B.c13639 CH CH 167
#kc_select CFSG.KD.M3B.c13639 PRf PR 136
#kc_select CFSG.KD.M3B.c13639 GKf GK 167
#kc_listDispatch CFSG.KD.M3B.c13639 Gf G 130

namespace CFSG.KD.M3B.c13639

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
  runP (tri m7BPairs n13639) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri m7BPairs n13639)) CH PRf Gf S0 (nat_lit 136) g

end CFSG.KD.M3B.c13639

#kc_each CFSG.KD.M3B.c13639.u 0 130

end
