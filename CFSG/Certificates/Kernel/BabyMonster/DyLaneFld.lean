module

public import CFSG.Certificates.Kernel.BabyMonster.DyLaneSpr
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.BM.Ln

open CFSG.KC.BM CFSG.KC.BM.Dy

theorem fld_eq_of_testBit {x y f g : ℕ} (h : ∀ r < 16, x.testBit (16 * f + r) = y.testBit (16 * g + r)) :
    fld x f = fld y g := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [fld_testBit, fld_testBit]
  by_cases hr : r < 16
  · rw [decide_eq_true hr, Bool.true_and, Bool.true_and, h r hr]
  · simp [hr]

theorem fld_eq_zero_of_testBit {x f : ℕ} (h : ∀ r < 16, x.testBit (16 * f + r) = false) : fld x f = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [fld_testBit, Nat.zero_testBit]
  by_cases hr : r < 16
  · rw [h r hr, Bool.and_false]
  · simp [hr]

theorem fld_xor (x y t : ℕ) : fld (x ^^^ y) t = fld x t ^^^ fld y t := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, fld_testBit, fld_testBit, fld_testBit, Nat.testBit_xor]
  cases decide (i < 16) <;> rfl

theorem fld_shr (z n f : ℕ) : fld (z >>> (16 * n)) f = fld z (f + n) := by
  rw [fld, fld, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  ring

theorem fld_shr256 (z f : ℕ) : fld (z >>> 256) f = fld z (f + 16) := fld_shr z 16 f

theorem fld_mul_pow (x t f : ℕ) : fld (x * 2 ^ (16 * t)) f = if t ≤ f then fld x (f - t) else 0 := by
  split
  · rename_i h
    rw [fld, fld, show 16 * f = 16 * t + 16 * (f - t) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · rename_i h
    apply fld_eq_zero_of_testBit
    intro r hr
    rw [Nat.testBit_mul_two_pow, decide_eq_false (by omega), Bool.false_and]

theorem fld_lnOne (t : ℕ) : fld lnOne t = if t < 16 then 1 else 0 := fld_rep (by decide) 16 t

theorem fld_lnMask {m : ℕ} (hm : 0 < m) (hm' : m ≤ 65536) (t : ℕ) :
    fld (lnMask m) t = if t < 16 * 4371 then m - 1 else 0 :=
  fld_rep (show m - 1 < 65536 by omega) _ t

theorem fld_lnOnes (t : ℕ) : fld lnOnes t = if t < 16 * 4371 then 1 else 0 := fld_rep (by decide) _ t

theorem fld_lnMaskP {m : ℕ} (hm : 0 < m) (hm' : m ≤ 256) (t : ℕ) :
    fld (lnMaskP m) t = if t < 16 * 4371 then m - 1 + 256 else 0 :=
  fld_rep (show m - 1 + 256 < 65536 by omega) _ t

theorem fld_land_LM (z t : ℕ) : fld (z &&& lnLM) t = if t < 16 then fld z t else 0 := by
  have hLM : lnLM = 2 ^ 256 - 1 := by
    unfold lnLM onesN
    rw [shl_one]
    rfl
  rw [hLM]
  split
  · rename_i h
    apply fld_eq_of_testBit
    intro r hr
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_true (by omega), Bool.and_true]
  · rename_i h
    apply fld_eq_zero_of_testBit
    intro r hr
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, decide_eq_false (by omega), Bool.and_false]

theorem fld_div_pow {e : ℕ} (he : e ≤ 16) (x f : ℕ) :
    fld (x / 2 ^ e) f = fld x f / 2 ^ e + 2 ^ (16 - e) * (fld x (f + 1) % 2 ^ e) := by
  set u := x / 2 ^ (16 * f) with hu
  have h1 : fld (x / 2 ^ e) f = u / 2 ^ e % 65536 := by
    rw [fld, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  have h2 : fld x f = u % 65536 := rfl
  have h3 : fld x (f + 1) = u / 65536 % 65536 := by
    rw [fld_succ]
    unfold fld
    rw [hu, Nat.div_div_eq_div_mul, Nat.mul_comm 65536, Nat.div_div_eq_div_mul x (2 ^ (16 * f)) 65536]
  rw [h1, h2, h3]
  have e16 : (65536 : ℕ) = 2 ^ e * 2 ^ (16 - e) := by rw [← Nat.pow_add, Nat.add_sub_cancel' he]
  have hu' := Nat.div_add_mod u 65536
  set a := u % 65536
  set b := u / 65536
  have ha : a < 65536 := Nat.mod_lt _ (by decide)
  have hpe : 0 < 2 ^ e := Nat.two_pow_pos e
  have hq : u / 2 ^ e = a / 2 ^ e + 2 ^ (16 - e) * b := by
    rw [← hu', e16, Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_left _ _ hpe, Nat.add_comm]
  rw [hq]
  have hb := Nat.div_add_mod b (2 ^ e)
  have hlt : a / 2 ^ e < 2 ^ (16 - e) := by
    rw [Nat.div_lt_iff_lt_mul hpe, Nat.mul_comm, ← e16]
    exact ha
  have : a / 2 ^ e + 2 ^ (16 - e) * b =
      (a / 2 ^ e + 2 ^ (16 - e) * (b % 2 ^ e)) + 65536 * (b / 2 ^ e) := by
    conv_lhs => rw [← hb]
    rw [e16]
    ring
  have hle : 2 ^ (16 - e) * (b % 2 ^ e) ≤ 2 ^ (16 - e) * (2 ^ e - 1) :=
    Nat.mul_le_mul_left _ (by have := Nat.mod_lt b hpe; omega)
  have h65 : 2 ^ (16 - e) * (2 ^ e - 1) + 2 ^ (16 - e) = 65536 := by
    rw [e16, Nat.mul_sub, Nat.mul_one, Nat.mul_comm (2 ^ e)]
    have : 2 ^ (16 - e) ≤ 2 ^ (16 - e) * 2 ^ e := Nat.le_mul_of_pos_right _ hpe
    omega
  have hdvd : 2 ^ e ∣ 65536 := ⟨2 ^ (16 - e), e16⟩
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega), Nat.mod_mod_of_dvd _ hdvd]

theorem fld_div_of_dvd {e : ℕ} (he : e ≤ 16) {x : ℕ} (hd : ∀ t, fld x t % 2 ^ e = 0) (t : ℕ) :
    fld (x / 2 ^ e) t = fld x t / 2 ^ e := by
  rw [fld_div_pow he, hd (t + 1), Nat.mul_zero, Nat.add_zero]

theorem fld_spr16 {b : ℕ} (hb : b < 2 ^ (8192 * 16)) (f : ℕ) :
    fld (lnSpr (lnKs 16 256) (lnD 16 256) b) f = if f % 16 = 0 then fld b (f / 16) else 0 := by
  have hs := testBit_spr (w := 16) (W := 256) (by decide) (by decide) hb
  split
  · rename_i h
    apply fld_eq_of_testBit
    intro r hr
    rw [hs]
    unfold lay
    have e : 16 * f + r = 256 * (f / 16) + r := by
      have := Nat.div_add_mod f 16
      omega
    rw [e, (div_mod_of rfl (by omega : r < 256)).1, (div_mod_of rfl (by omega : r < 256)).2,
      decide_eq_true hr, Bool.true_and, Nat.mul_comm]
  · rename_i h
    apply fld_eq_zero_of_testBit
    intro r hr
    rw [hs]
    unfold lay
    have e : 16 * f + r = 256 * (f / 16) + (16 * (f % 16) + r) := by
      have := Nat.div_add_mod f 16
      omega
    rw [e, (div_mod_of rfl (by omega : 16 * (f % 16) + r < 256)).2,
      decide_eq_false (by omega), Bool.false_and]

theorem eq_sum_fld : ∀ (n : ℕ) {x : ℕ}, x < 2 ^ (16 * n) →
    x = ∑ t ∈ Finset.range n, fld x t * 2 ^ (16 * t)
  | 0, x, hx => by simpa using hx
  | n + 1, x, hx => by
    have h1 : x / 65536 < 2 ^ (16 * n) := by
      rw [Nat.div_lt_iff_lt_mul (by decide), show (65536 : ℕ) = 2 ^ 16 from rfl, ← Nat.pow_add]
      rw [show 16 * n + 16 = 16 * (n + 1) by ring]
      exact hx
    have ih := eq_sum_fld n h1
    rw [Finset.sum_range_succ']
    have e : ∑ t ∈ Finset.range n, fld x (t + 1) * 2 ^ (16 * (t + 1)) =
        65536 * ∑ t ∈ Finset.range n, fld (x / 65536) t * 2 ^ (16 * t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [fld_succ, show 16 * (t + 1) = 16 * t + 16 by ring, Nat.pow_add]
      ring
    rw [e, ← ih, fld_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    omega

theorem fld_mulSpr {NQ Sb : ℕ} (hNQ : NQ < 2 ^ 256) (hn : ∀ t, fld NQ t ≤ 256)
    (hS : ∀ f, f % 16 ≠ 0 → fld Sb f = 0) (hS' : ∀ k, fld Sb (16 * k) ≤ 128) {t : ℕ} (ht : t < 16)
    (k : ℕ) : fld (NQ * Sb) (16 * k + t) = fld NQ t * fld Sb (16 * k) := by
  have key : ∀ T ≤ 16, ∀ k t, t < 16 →
      fld ((∑ u ∈ Finset.range T, fld NQ u * 2 ^ (16 * u)) * Sb) (16 * k + t) =
        if t < T then fld NQ t * fld Sb (16 * k) else 0 := by
    intro T
    induction T with
    | zero =>
      intro _ k t _
      simp [fld]
    | succ T ih =>
      intro hT k t ht
      have hterm : ∀ f, fld (fld NQ T * 2 ^ (16 * T) * Sb) f =
          if T ≤ f ∧ (f - T) % 16 = 0 then fld NQ T * fld Sb (f - T) else 0 := by
        intro f
        rw [show fld NQ T * 2 ^ (16 * T) * Sb = fld NQ T * (Sb * 2 ^ (16 * T)) by ring,
          fld_mul _ (fun f' => by
            rw [fld_mul_pow]
            split
            · rename_i h
              by_cases h0 : (f' - T) % 16 = 0
              · obtain ⟨k', hk'⟩ : ∃ k', f' - T = 16 * k' := ⟨(f' - T) / 16, by omega⟩
                rw [hk']
                calc fld NQ T * fld Sb (16 * k') ≤ 256 * 128 := Nat.mul_le_mul (hn T) (hS' k')
                  _ < 65536 := by decide
              · rw [hS _ h0, Nat.mul_zero]
                decide
            · rw [Nat.mul_zero]
              decide), fld_mul_pow]
        by_cases h1 : T ≤ f
        · by_cases h2 : (f - T) % 16 = 0
          · rw [ite_eq_left h1, ite_eq_left ⟨h1, h2⟩]
          · rw [ite_eq_left h1, ite_eq_right (fun h => h2 h.2), hS _ h2, Nat.mul_zero]
        · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.1), Nat.mul_zero]
      rw [Finset.sum_range_succ, Nat.add_mul]
      have hsum : ∀ f, fld ((∑ u ∈ Finset.range T, fld NQ u * 2 ^ (16 * u)) * Sb) f +
          fld (fld NQ T * 2 ^ (16 * T) * Sb) f < 65536 := by
        intro f
        have hf := Nat.div_add_mod f 16
        rw [show f = 16 * (f / 16) + f % 16 by omega, ih (by omega) _ _ (Nat.mod_lt _ (by decide)),
          hterm]
        have hb1 : fld NQ (f % 16) * fld Sb (16 * (f / 16)) ≤ 256 * 128 :=
          Nat.mul_le_mul (hn _) (hS' _)
        split
        · rename_i hlt
          have hn2 : ¬(T ≤ 16 * (f / 16) + f % 16 ∧ (16 * (f / 16) + f % 16 - T) % 16 = 0) := by
            rintro ⟨h1, h2⟩
            omega
          rw [ite_eq_right hn2]
          omega
        · split
          · rename_i _ hh
            have := Nat.mul_le_mul (hn T) (hS' ((16 * (f / 16) + f % 16 - T) / 16))
            rw [show 16 * ((16 * (f / 16) + f % 16 - T) / 16) = 16 * (f / 16) + f % 16 - T by omega]
              at this
            omega
          · omega
      rw [fld_add _ hsum, ih (by omega) k t ht, hterm]
      by_cases htT : t < T
      · have hn2 : ¬(T ≤ 16 * k + t ∧ (16 * k + t - T) % 16 = 0) := by
          rintro ⟨h1, h2⟩
          omega
        rw [ite_eq_left htT, ite_eq_right hn2, ite_eq_left (by omega : t < T + 1), Nat.add_zero]
      · by_cases htT' : t = T
        · subst htT'
          have hc : t ≤ 16 * k + t ∧ (16 * k + t - t) % 16 = 0 := ⟨by omega, by omega⟩
          rw [ite_eq_right htT, ite_eq_left hc, ite_eq_left (by omega : t < t + 1),
            show 16 * k + t - t = 16 * k by omega, Nat.zero_add]
        · have hn2 : ¬(T ≤ 16 * k + t ∧ (16 * k + t - T) % 16 = 0) := by
            rintro ⟨h1, h2⟩
            omega
          rw [ite_eq_right htT, ite_eq_right hn2, ite_eq_right (by omega : ¬ t < T + 1)]
  have e := eq_sum_fld 16 hNQ
  have h2 : NQ * Sb = (∑ u ∈ Finset.range 16, fld NQ u * 2 ^ (16 * u)) * Sb := congrArg (· * Sb) e
  rw [h2]
  exact (key 16 le_rfl k t ht).trans (ite_eq_left ht)

end CFSG.KC.BM.Ln

end
