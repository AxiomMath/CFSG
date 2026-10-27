module

public import Certificates.Data.Kernel.Fi22Twist.Tf
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

theorem strictB_eqT (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem tf_sound {T TT S : Nat → Nat} {n : Nat} (h : ∀ f < n, tfK T TT S f = true)
    (Q : (Nat → Nat) → Prop) (h0 : ∀ φ : Nat → Nat, (∀ x < 3510, φ x = x) → Q φ)
    (hs : ∀ j < 19, ∀ φ ψ : Nat → Nat, Q ψ → (∀ x < 3510, φ x = ap (S j) (ψ x)) → Q φ) :
    ∀ f < n, Q (ap (T f)) := by
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
    intro hf
    have hc := h f hf
    unfold tfK at hc
    rw [strictB_eqT, strictB_eqT] at hc
    cases hb : Nat.beq (fld(TT f, 8, 65535)) 0
    · rw [hb] at hc
      change Bool.rec (motive := fun _ => Bool) false _ _ = true at hc
      obtain ⟨h1, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      obtain ⟨h2, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      rw [strictB_eqT, strictB_eqT] at hc
      have hpar : fld(TT f, 24, 65535) < f := Nat.le_of_ble_eq_true h1
      have hj : Nat.shiftRight (TT f) 40 < 19 := Nat.le_of_ble_eq_true h2
      refine hs _ hj _ _ (ih _ hpar (Nat.lt_trans hpar hf)) fun x hx => ?_
      exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hc x hx)
    · rw [hb] at hc
      exact h0 _ fun x hx => Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hc x hx)

end CFSG.KC.Fi22Twist

end
