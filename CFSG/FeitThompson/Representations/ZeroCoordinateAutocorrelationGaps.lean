module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Finset

namespace CyclicAutocorrelation

variable {r : ℕ} [NeZero r]

lemma sum_comp_add_right {M : Type*} [AddCommMonoid M] (f : ZMod r → M) (m : ZMod r) :
    ∑ i, f (i + m) = ∑ i, f i :=
  Fintype.sum_equiv (Equiv.addRight m) _ _ fun _ => rfl

lemma sum_comp_add_left {M : Type*} [AddCommMonoid M] (f : ZMod r → M) (i : ZMod r) :
    ∑ m, f (i + m) = ∑ m, f m :=
  Fintype.sum_equiv (Equiv.addLeft i) _ _ fun _ => rfl

def autocorr (n : ZMod r → ℕ) (m : ZMod r) : ℕ := ∑ i, n i * n (i + m)

@[simp]
lemma autocorr_apply (n : ZMod r → ℕ) (m : ZMod r) :
    autocorr n m = ∑ i, n i * n (i + m) := (rfl)

lemma autocorr_zero (n : ZMod r → ℕ) : autocorr n 0 = ∑ i, n i ^ 2 := by
  simp [sq]

lemma autocorr_neg (n : ZMod r → ℕ) (m : ZMod r) : autocorr n (-m) = autocorr n m := by
  have h := sum_comp_add_right (fun i => n i * n (i + -m)) m
  simp only [autocorr_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by
    rw [add_assoc, add_neg_cancel, add_zero, mul_comm]

lemma sum_autocorr (n : ZMod r → ℕ) : ∑ m, autocorr n m = (∑ i, n i) ^ 2 := by
  simp only [autocorr_apply]
  rw [Finset.sum_comm]
  calc ∑ i, ∑ m, n i * n (i + m) = ∑ i, n i * ∑ m, n m := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, sum_comp_add_left]
    _ = (∑ i, n i) ^ 2 := by rw [← Finset.sum_mul, sq]

lemma cast_autocorr (n : ZMod r → ℕ) (m : ZMod r) :
    ((autocorr n m : ℕ) : ℤ) = ∑ i, (n i : ℤ) * (n (i + m) : ℤ) := by
  rw [autocorr_apply]; push_cast; ring

lemma sum_sq_sub_shift {n : ZMod r → ℕ}
    (hgap : ∀ m : ZMod r, m ≠ 0 → autocorr n 0 = autocorr n m + 1) {m : ZMod r} (hm : m ≠ 0) :
    ∑ i, ((n i : ℤ) - (n (i + m) : ℤ)) ^ 2 = 2 := by
  have hshift : ∑ i, ((n (i + m) : ℤ)) ^ 2 = ∑ i, ((n i : ℤ)) ^ 2 :=
    sum_comp_add_right (fun j => ((n j : ℤ)) ^ 2) m
  have h0 : ((autocorr n 0 : ℕ) : ℤ) = ∑ i, ((n i : ℤ)) ^ 2 := by
    rw [autocorr_zero]; push_cast; ring
  have hgap' : ((autocorr n 0 : ℕ) : ℤ) = ((autocorr n m : ℕ) : ℤ) + 1 := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) (hgap m hm)
  calc ∑ i, ((n i : ℤ) - (n (i + m) : ℤ)) ^ 2
      = ∑ i, (((n i : ℤ)) ^ 2 + ((n (i + m) : ℤ)) ^ 2
          - 2 * ((n i : ℤ) * (n (i + m) : ℤ))) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = ((∑ i, ((n i : ℤ)) ^ 2) + ∑ i, ((n (i + m) : ℤ)) ^ 2)
          - 2 * ∑ i, ((n i : ℤ) * (n (i + m) : ℤ)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = 2 := by rw [hshift, ← h0, ← cast_autocorr]; linarith

theorem coord_eq_zero_or_one {n : ZMod r → ℕ} (h0 : n 0 = 0)
    (hgap : ∀ m : ZMod r, m ≠ 0 → autocorr n 0 = autocorr n m + 1) (i : ZMod r) :
    n i = 0 ∨ n i = 1 := by
  rcases eq_or_ne i 0 with rfl | hi
  · exact Or.inl h0
  · have key := sum_sq_sub_shift hgap hi
    have hterm : ((n 0 : ℤ) - (n (0 + i) : ℤ)) ^ 2
        ≤ ∑ j, ((n j : ℤ) - (n (j + i) : ℤ)) ^ 2 :=
      Finset.single_le_sum (f := fun j => ((n j : ℤ) - (n (j + i) : ℤ)) ^ 2)
        (fun _ _ => sq_nonneg _) (mem_univ 0)
    rw [key, h0, zero_add] at hterm
    have hle : n i ≤ 1 := by
      by_contra hcon
      have h2 : (2 : ℤ) ≤ (n i : ℤ) := by exact_mod_cast (by omega : 2 ≤ n i)
      push_cast at hterm
      nlinarith
    omega

theorem sum_eq_one_or_eq_card_sub_one {n : ZMod r → ℕ} (hr : 2 ≤ r) (h0 : n 0 = 0)
    (hgap : ∀ m : ZMod r, m ≠ 0 → autocorr n 0 = autocorr n m + 1) :
    (∑ i, n i) = 1 ∨ (∑ i, n i) = r - 1 := by
  set d : ℕ := ∑ i, n i with hdef
  have hr1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
    have h1 : (1 : ℕ) ≤ r := by omega
    push_cast [h1]; ring
  have hsq : autocorr n 0 = d := by
    rw [autocorr_zero, hdef]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases coord_eq_zero_or_one h0 hgap i with h | h <;> simp [h]
  have hm : ∀ m : ZMod r, m ≠ 0 → ((autocorr n m : ℕ) : ℤ) = (d : ℤ) - 1 := by
    intro m hmne
    have h := hgap m hmne
    rw [hsq] at h
    omega
  have hcard : (Finset.univ.erase (0 : ZMod r)).card = r - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ZMod.card]
  have hsum : ∑ m, ((autocorr n m : ℕ) : ℤ) = (d : ℤ) + ((r : ℤ) - 1) * ((d : ℤ) - 1) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod r)),
      Finset.sum_congr rfl (fun m hmem => hm m (Finset.ne_of_mem_erase hmem)),
      Finset.sum_const, hcard, hsq, nsmul_eq_mul, hr1]
  have htotal : ((d : ℤ)) ^ 2 = (d : ℤ) + ((r : ℤ) - 1) * ((d : ℤ) - 1) := by
    rw [← hsum, ← Nat.cast_sum, sum_autocorr, ← hdef]
    push_cast
    ring
  have hfac : ((d : ℤ) - 1) * ((d : ℤ) - ((r : ℤ) - 1)) = 0 := by nlinarith
  rcases mul_eq_zero.1 hfac with h | h
  · left; omega
  · right
    have hcast : (d : ℤ) = ((r - 1 : ℕ) : ℤ) := by rw [hr1]; linarith
    exact_mod_cast hcast

lemma sum_pos_of_gap {n : ZMod r → ℕ} (hr : 2 ≤ r)
    (hgap : ∀ m : ZMod r, m ≠ 0 → autocorr n 0 = autocorr n m + 1) : 0 < ∑ i, n i := by
  rcases Nat.eq_zero_or_pos (∑ i, n i) with h | h
  · exfalso
    have hone : (1 : ZMod r) ≠ 0 := by
      have : Fact (1 < r) := ⟨hr⟩
      exact one_ne_zero
    have hzero : ∀ i, n i = 0 := fun i => (Finset.sum_eq_zero_iff).1 h i (mem_univ i)
    have h1 := hgap 1 hone
    simp [hzero] at h1
  · exact h

end CyclicAutocorrelation

end

end CFSG.FeitThompson
