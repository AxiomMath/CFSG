module

public import Certificates.Data.Kernel.HeAutK

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum

theorem cntR_succ (f : Nat → Bool) (lo k : Nat) :
    cntR f lo (k + 1) = cntR f lo k + Bool.rec (motive := fun _ => Nat) 0 1 (f (lo + k)) := by
  have h : ∀ y c, strictN y (fun a => Nat.add a c) = y + c := fun y c => by cases y <;> rfl
  exact h _ _

theorem cntR_add (f : Nat → Bool) (lo a b : Nat) :
    cntR f lo (a + b) = cntR f lo a + cntR f (lo + a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [← Nat.add_assoc, cntR_succ, ih, cntR_succ, Nat.add_assoc, Nat.add_assoc lo a b]

theorem allR_add (f : Nat → Bool) (lo a b : Nat) :
    allR f lo (a + b) = (allR f lo a && allR f (lo + a) b) := by
  induction b with
  | zero =>
    have h0 : allR f (lo + a) 0 = true := rfl
    rw [Nat.add_zero, h0, Bool.and_true]
  | succ b ih =>
    have h : ∀ lo k, allR f lo (k + 1) = (allR f lo k && f (lo + k)) := fun _ _ => rfl
    rw [← Nat.add_assoc, h, ih, h, Bool.and_assoc, Nat.add_assoc lo a b]

end CFSG.KC.HeAutK

end
