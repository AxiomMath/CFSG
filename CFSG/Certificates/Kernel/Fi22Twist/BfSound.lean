module

public import Certificates.Data.Kernel.Fi22Twist.Bf
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

theorem strictB_eqB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem allBlk_spec0 {f : Nat → Bool} {len : Nat} (h : allBlk 0 f len = true) :
    ∀ l < len, f l = true := by
  intro l hl
  have e := CFSG.KS.allBlk_spec h l hl
  have e0 : Nat.add 0 l = l := Nat.zero_add l
  rwa [e0] at e

theorem bf_root {BF S : Nat → Nat} (h : bfK BF S 0 = true) :
    fld(BF 0, 0, 4095) = 3 ∧ fld(BF 0, 12, 4095) = 6 := by
  unfold bfK at h
  rw [strictB_eqB] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem bf_sound {BF S : Nat → Nat} {n : Nat} (h : ∀ k < n, bfK BF S k = true)
    (Q : (Nat → Nat) → Prop) (h0 : ∀ φ : Nat → Nat, (∀ x < 3510, φ x = x) → Q φ)
    (hs : ∀ j < 19, ∀ φ ψ : Nat → Nat, Q ψ → (∀ x < 3510, φ x = ap (S j) (ψ x)) → Q φ) :
    ∀ k < n, ∃ φ : Nat → Nat, Q φ ∧ (∀ m < 3, φ (bp m) = bp m) ∧
      ∀ p < 9, fld(BF k, Nat.mul 12 p, 4095) = φ (fld(BF 0, Nat.mul 12 p, 4095)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨fun x => x, h0 _ fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    have hc := h k hk
    unfold bfK at hc
    rw [strictB_eqB] at hc
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hb : Nat.beq k 0 = false := by
      rw [hk']
      rfl
    rw [hb] at hc
    change Bool.rec (motive := fun _ => Bool) false _ _ = true at hc
    obtain ⟨h1, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    obtain ⟨h2, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    rw [strictB_eqB, strictB_eqB] at hc
    obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    have hpar : fld(BF k, 108, 4095) < k := Nat.le_of_ble_eq_true h1
    have hj : Nat.shiftRight (BF k) 120 < 19 := Nat.le_of_ble_eq_true h2
    obtain ⟨ψ, hQ, hfix, hpt⟩ := ih _ hpar (Nat.lt_trans hpar hk)
    refine ⟨fun x => ap (S (Nat.shiftRight (BF k) 120)) (ψ x),
      hs _ hj _ _ hQ fun _ _ => rfl, fun m hm => ?_, fun p hp => ?_⟩
    · change ap (S (Nat.shiftRight (BF k) 120)) (ψ (bp m)) = bp m
      rw [hfix m hm]
      exact Nat.eq_of_beq_eq_true (allBlk_spec0 h3 m hm)
    · change _ = ap (S (Nat.shiftRight (BF k) 120)) (ψ (fld(BF 0, Nat.mul 12 p, 4095)))
      rw [← hpt p hp]
      exact Nat.eq_of_beq_eq_true (allBlk_spec0 h4 p hp)

end CFSG.KC.Fi22Twist

end
