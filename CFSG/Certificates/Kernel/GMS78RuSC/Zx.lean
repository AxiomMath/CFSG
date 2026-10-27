module

public import Certificates.Data.Kernel.GMS78RuSCent
import CFSG.Certificates.Kernel.GMS78RuP.Basic

public section

namespace CFSG.KC.GMS.SC

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def zxLoop (rows : List Nat) (iu i2 n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => strictN acc fun a =>
        (fun Ri => (fun f1 f2 => Nat.add a (Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 f1)
            (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 f2) 9)))
          (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
              (Nat.beq pq (fget (neGet 0 rows iu) qp 8))) (fget Ri j 8) (fget (neGet 0 rows j) i 8))
          (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
              (Nat.beq pq (fget (neGet 0 rows i2) qp 8))) (fget Ri j 8) (fget (neGet 0 rows j) i 8)))
        (neGet 0 rows i)) n

@[expose] noncomputable def rowsR (m : Nat → Nat → Nat) (IDX : Nat) (C : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons (czPack8 (List.rec (motive := fun _ => List Nat) []
        (fun q _ ih2 => List.cons (Nat.sub (fget IDX (m p q) 9) 1) ih2) C)) ih) C

theorem sZx_def0 (m : Nat → Nat → Nat) (C : List Nat) (u : Nat) :
    sZx m C u = zxLoop (List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons (czPack8 (List.rec (motive := fun _ => List Nat) []
        (fun q _ ih2 => List.cons (Nat.sub (fget (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 9 x)) (ih (Nat.succ i))) C 0) (m p q) 9) 1) ih2) C)) ih) C)
      (Nat.sub (fget (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 9 x)) (ih (Nat.succ i))) C 0) u 9) 1)
      (Nat.sub (fget (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.lor (Nat.shiftLeft (Nat.succ i) (Nat.mul 9 x)) (ih (Nat.succ i))) C 0) 256 9) 1)
      (nat_lit 256) := rfl

theorem sZx_def (m : Nat → Nat → Nat) (C : List Nat) (u : Nat) :
    sZx m C u = zxLoop (rowsR m (sIdx C) C) (Nat.sub (fget (sIdx C) u 9) 1)
      (Nat.sub (fget (sIdx C) 256 9) 1) (nat_lit 256) := sZx_def0 m C u

@[expose] noncomputable def cnt8 (rows : List Nat) (i ι : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 1
    (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
      (Nat.beq pq (fget (neGet 0 rows ι) qp 8))) (fget (neGet 0 rows i) j 8)
        (fget (neGet 0 rows j) i 8))

theorem zxLoop_eq (rows : List Nat) (iu i2 : Nat) : ∀ n : Nat, zxLoop rows iu i2 n =
    ((List.range n).map (fun i => cnt8 rows i iu + (cnt8 rows i i2) <<< 9)).sum
  | 0 => rfl
  | n + 1 => by
    unfold zxLoop
    dsimp only
    change strictN (zxLoop rows iu i2 n) _ = _
    rw [P117.strictN_eq, zxLoop_eq rows iu i2 n, List.range_succ, List.map_append, List.sum_append]
    rfl

@[expose] noncomputable def zxTLoop (R T : List Nat) (Rt : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => strictN ih fun a =>
    (fun Ri Ti => Nat.add a (Bool.rec (motive := fun _ => Nat) 0 1
      (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
          (Nat.beq pq (fget Rt (Nat.sub qp 1) 9))) (fget Ri j 9) (fget Ti j 9))))
      (neGet 0 R i) (neGet 0 T i)) L

theorem sZxT_def (R T : List Nat) (Rt : Nat) : sZxT R T Rt = zxTLoop R T Rt (List.range' 0 256) := rfl

@[expose] noncomputable def cntT (R T : List Nat) (Rt i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 1
    (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
          (Nat.beq pq (fget Rt (Nat.sub qp 1) 9))) (fget (neGet 0 R i) j 9) (fget (neGet 0 T i) j 9))

theorem zxTLoop_eq (R T : List Nat) (Rt : Nat) : ∀ L : List Nat,
    zxTLoop R T Rt L = (L.map (cntT R T Rt)).sum
  | [] => rfl
  | i :: L => by
    unfold zxTLoop
    dsimp only
    change strictN (zxTLoop R T Rt L) _ = _
    rw [P117.strictN_eq, zxTLoop_eq R T Rt L, List.map_cons, List.sum_cons]
    exact Nat.add_comm _ _

theorem sZxT_eq (R T : List Nat) (Rt : Nat) :
    sZxT R T Rt = ((List.range 256).map (cntT R T Rt)).sum := by
  rw [sZxT_def, zxTLoop_eq, List.range_eq_range']

end CFSG.KC.GMS.SC

end
