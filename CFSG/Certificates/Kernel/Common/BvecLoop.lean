module

public import CFSG.Monster.Code.Bits
public import Mathlib.Data.Nat.Count

public section

namespace CFSG.KC.BvecLoop

open CFSG.Monster.Code

theorem bvec_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) (h : bvec n x = bvec n y) :
    x = y := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < n
  · have e := congrFun h ⟨i, hi⟩
    simp only [bvec] at e
    cases hx' : x.testBit i <;> cases hy' : y.testBit i <;> simp_all
  · have hn : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hn), Nat.testBit_lt_two_pow (lt_of_lt_of_le hy hn)]

theorem exists_bvec : ∀ (n : ℕ) (v : Fin n → ZMod 2), ∃ x < 2 ^ n, bvec n x = v
  | 0, v => ⟨0, by norm_num, funext fun i => i.elim0⟩
  | n + 1, v => by
    obtain ⟨x, hx, e⟩ := exists_bvec n (fun i => v i.succ)
    refine ⟨Nat.bit (decide (v 0 = 1)) x, ?_, funext fun i => ?_⟩
    · rw [Nat.bit_val, pow_succ]
      cases decide (v 0 = 1) <;> simp <;> omega
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [bvec, Fin.val_zero, Nat.testBit_bit_zero]
        generalize v 0 = a
        revert a
        decide
      · simp only [bvec, Fin.val_succ, Nat.testBit_bit_succ]
        exact congrFun e j

theorem forall_bvec {n : ℕ} {P : (Fin n → ZMod 2) → Prop} :
    (∀ v, P v) ↔ ∀ x < 2 ^ n, P (bvec n x) := by
  refine ⟨fun h x _ => h _, fun h v => ?_⟩
  obtain ⟨x, hx, rfl⟩ := exists_bvec n v
  exact h x hx

theorem card_filter_bvec {n : ℕ} (P : (Fin n → ZMod 2) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = Nat.count (fun x => P (bvec n x)) (2 ^ n) := by
  rw [Nat.count_eq_card_filter_range]
  symm
  refine Finset.card_bij (fun x _ => bvec n x) (fun x hx => ?_) (fun x hx y hy e => ?_)
    (fun v hv => ?_)
  · simp only [Finset.mem_filter, Finset.mem_range] at hx
    simpa using hx.2
  · simp only [Finset.mem_filter, Finset.mem_range] at hx hy
    exact bvec_inj hx.1 hy.1 e
  · obtain ⟨x, hx, rfl⟩ := exists_bvec n v
    exact ⟨x, by simpa [hx] using hv, rfl⟩

end CFSG.KC.BvecLoop
