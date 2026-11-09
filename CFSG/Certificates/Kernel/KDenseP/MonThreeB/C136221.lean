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

#kc_plan CFSG.KD.M3B.c136221 "c136221.plan.txt" 9327 12906655729232901777
#kc_plan CFSG.KD.M3B.c136221 "c136221.grp.txt" 7433 6237470432468278860
#kc_repo #kc_ktree CFSG.KD.M3B.c136221 RT "CFSG/Certificates/Kernel/KDenseP/MonThreeB/c136221.rec.bin" 129721 4
  26852247 14265911091324871286
#kc_select CFSG.KD.M3B.c136221 CH CH 261
#kc_select CFSG.KD.M3B.c136221 PRf PR 210
#kc_select CFSG.KD.M3B.c136221 GKf GK 261
#kc_listDispatch CFSG.KD.M3B.c136221 Gf G 198

namespace CFSG.KD.M3B.c136221

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
  runP (tri e136221 []) (f20 c (nat_lit 0)) c s

@[expose] noncomputable def u (g : Nat) : Bool :=
  grpL rn (chkP (tri e136221 [])) CH PRf Gf S0 (nat_lit 210) g

end CFSG.KD.M3B.c136221

#kc_each CFSG.KD.M3B.c136221.u 0 198

end
