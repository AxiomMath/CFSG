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

#kc_plan CFSG.KD.M3B.c136220 "c136220.plan.txt" 6944 14304639427447999029
#kc_plan CFSG.KD.M3B.c136220 "c136220.grp.txt" 6247 12387104164643446788
#kc_repo #kc_ktree CFSG.KD.M3B.c136220 RT "CFSG/Certificates/Kernel/KDenseP/MonThreeB/c136220.rec.bin" 129721 4
  23738943 15494186606540926002
#kc_select CFSG.KD.M3B.c136220 CH CH 207
#kc_select CFSG.KD.M3B.c136220 PRf PR 186
#kc_select CFSG.KD.M3B.c136220 GKf GK 207
#kc_listDispatch CFSG.KD.M3B.c136220 Gf G 183

namespace CFSG.KD.M3B.c136220

open CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.MonThreeB

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
  runP (tri e136220 []) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e136220 [])) CH PRf Gf S0 (nat_lit 186) g

end CFSG.KD.M3B.c136220

#kc_each CFSG.KD.M3B.c136220.u 0 183

end
