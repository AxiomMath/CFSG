module

public import Certificates.Data.Kernel.Co1BFix
public import CFSG.Certificates.Kernel.Co1BBoundPSound

public section

namespace CFSG.KC.Co1B

open CFSG.KC.M1F2 CFSG.KC.Enum CFSG.KC.Co1BBoundP

@[expose] noncomputable def zeroCntP (Z : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (Nat.beq (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) Z k) (nat_lit 0))) n

@[expose] noncomputable def fixChunkP (T P : Nat) : Nat :=
  zeroCntP (Nat.xor (vmP ONES T P) P) (nat_lit 840)

@[expose] noncomputable def fixTabP (T : Nat) (F : Nat → Nat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun j acc => Nat.add (fixChunkP T (F j)) acc) m

theorem beq_xor_zeroP (a b : Nat) : Nat.beq (Nat.xor a b) 0 = Nat.beq a b := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, Nat.beq_eq]
  change a ^^^ b = 0 ↔ a = b
  constructor
  · intro h
    calc a = (a ^^^ b) ^^^ b := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      _ = b := by rw [h, Nat.zero_xor]
  · rintro rfl
    exact Nat.xor_self a

theorem zeroCntP_eq (T P : Nat) : ∀ n ≤ 840, zeroCntP (Nat.xor (vmP ONES T P) P) n =
    Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => (fun v =>
      Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc) (Nat.beq (vmF (nat_lit 24) T v) v))
        (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)) n := by
  intro n hn
  unfold zeroCntP
  refine cnt_congr (nat_lit 0)
    (fun k => Nat.beq (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) (Nat.xor (vmP ONES T P) P) k)
      (nat_lit 0))
    (fun k => Nat.beq (vmF (nat_lit 24) T (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k))
      (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)) n fun k hk => ?_
  have e := pg_vmP T P (Nat.lt_of_lt_of_le hk hn)
  rw [pg_eq, pg_eq] at e
  change Nat.beq (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) (Nat.xor (vmP ONES T P) P) k)
    (nat_lit 0) = Nat.beq (vmF (nat_lit 24) T (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k))
      (pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k)
  rw [pg_eq, pg_eq]
  change Nat.beq (fd24 (vmP ONES T P ^^^ P) k) 0 = _
  rw [fd24_xor, e]
  exact beq_xor_zeroP _ _

theorem fixChunkP_eq (T P : Nat) : fixChunkP T P = fixChunkK T P := by
  unfold fixChunkP fixChunkK
  exact zeroCntP_eq T P (nat_lit 840) (Nat.le_refl 840)

theorem fixTabP_eq (T : Nat) (F : Nat → Nat) (m : Nat) : fixTabP T F m = fixTabK T F m := by
  unfold fixTabP fixTabK
  induction m with
  | zero => rfl
  | succ m ih =>
    change Nat.add (fixChunkP T (F m)) _ = Nat.add (fixChunkK T (F m)) _
    rw [ih, fixChunkP_eq]

end CFSG.KC.Co1B

end
