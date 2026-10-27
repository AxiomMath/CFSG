module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Three7

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf11

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

variable {n : ℕ}

@[expose] def evenVec (n : ℕ) : Subgroup (Wr n) where
  carrier := {a | a.perm = 1 ∧ wsum a = 0}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [mul_perm, ha.1, hb.1, one_mul]
    · rw [wsum_mul, ha.2, hb.2, add_zero]
  one_mem' := ⟨rfl, wsum_one⟩
  inv_mem' {a} ha := ⟨by rw [inv_perm, ha.1, inv_one], by rw [wsum_inv]; exact ha.2⟩

theorem ofVec_add (u v : Fin n → ZMod 2) : ofVec (u + v) = ofVec u * ofVec v := by
  refine Wr.ext (funext fun x => ?_) rfl
  rfl

theorem pairVec_apply_left (x y : Fin n) (hxy : x ≠ y) : pairVec x y x = 1 := by
  unfold pairVec; simp [hxy]

theorem pairVec_apply_other (x y z : Fin n) (hx : z ≠ x) (hy : z ≠ y) : pairVec x y z = 0 := by
  unfold pairVec; simp [hx, hy]

theorem sum_pairVec (x y : Fin n) : ∑ i, pairVec x y i = 0 := by
  have := (ofVec_pairVec_mem x y).1
  exact this

theorem evenVec_le_closure (C : Subgroup (Wr n)) (h : ∀ x y : Fin n, ofVec (pairVec x y) ∈ C) :
    evenVec n ≤ C := by
  classical
  intro a ha
  have hae : a = ofVec a.vec := Wr.ext rfl ha.1
  rw [hae]
  have hsum : ∑ i, a.vec i = 0 := ha.2
  suffices H : ∀ k : ℕ, ∀ w : Fin n → ZMod 2, ∑ i, w i = 0 →
      (Finset.univ.filter fun i => w i ≠ 0).card = k → ofVec w ∈ C from
    H _ a.vec hsum rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro w hw hk
    by_cases hz : ∀ i, w i = 0
    · have : w = 0 := funext hz
      rw [this]
      have : ofVec (0 : Fin n → ZMod 2) = 1 := rfl
      rw [this]; exact C.one_mem
    · push Not at hz
      obtain ⟨x, hx⟩ := hz
      have hx1 : w x = 1 := by
        revert hx; generalize w x = t; revert t; decide
      obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ w y ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have : ∑ i, w i = w x := by
          rw [Finset.sum_eq_single x]
          · intro b _ hb; exact hcon b hb
          · simp
        rw [this, hx1] at hw
        exact absurd hw (by decide)
      have hy1 : w y = 1 := by
        revert hy; generalize w y = t; revert t; decide
      set w' := w + pairVec x y with hw'
      have hw'sum : ∑ i, w' i = 0 := by
        rw [hw']
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [hw, sum_pairVec, add_zero]
      have hlt : (Finset.univ.filter fun i => w' i ≠ 0).card < k := by
        rw [← hk]
        apply Finset.card_lt_card
        refine ⟨?_, ?_⟩
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          by_cases hzx : z = x
          · subst hzx; rw [hx1]; decide
          · by_cases hzy : z = y
            · subst hzy; rw [hy1]; decide
            · rw [hw', Pi.add_apply, pairVec_apply_other x y z hzx hzy, add_zero] at hz
              exact hz
        · intro hsub
          have := hsub (show x ∈ Finset.univ.filter fun i => w i ≠ 0 by simp [hx1])
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          rw [hw', Pi.add_apply, pairVec_apply_left x y (Ne.symm hyx), hx1] at this
          exact this (by decide)
      have hm := ih _ hlt w' hw'sum rfl
      have hww : w = pairVec x y + w' := by
        funext i
        rw [hw', Pi.add_apply, Pi.add_apply]
        have := zmod_two_add_self (pairVec x y i)
        calc w i = (pairVec x y i + pairVec x y i) + w i := by rw [this, zero_add]
          _ = pairVec x y i + (w i + pairVec x y i) := by ring
      rw [hww, ofVec_add]
      exact C.mul_mem (h x y) hm

theorem pairVec_trans (x y t : Fin n) : pairVec x y = pairVec x t + pairVec t y := by
  funext i
  unfold pairVec
  simp only [Pi.add_apply]
  generalize (if i = x then (1 : ZMod 2) else 0) = a
  generalize (if i = y then (1 : ZMod 2) else 0) = b
  generalize (if i = t then (1 : ZMod 2) else 0) = c
  revert a b c; decide

theorem pairVec_comm (x y : Fin n) : pairVec x y = pairVec y x := by
  funext i; unfold pairVec; exact add_comm _ _

theorem pairVec_self (x : Fin n) : pairVec x x = 0 := by
  funext i; unfold pairVec; exact zmod_two_add_self _

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf11
