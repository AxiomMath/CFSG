module

public import CFSG.Certificates.Kernel.OmegaCY.Hom
public import Mathlib.Tactic.IntervalCases

namespace CFSG.KC.OmegaCY

theorem ss_bIf (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem ss_allR {n : ℕ} {f : ℕ → Bool} (h : allR n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    have h' : (f n && allR n f) = true := (cy_bAndD _ _).symm.trans h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact ih h'.2 i hi
    · exact h'.1

theorem ss_anyR {n : ℕ} {f : ℕ → Bool} (h : anyR n f = true) : ∃ i < n, f i = true := by
  induction n with
  | zero => exact absurd h Bool.false_ne_true
  | succ n ih =>
    have h' : (if f n = true then true else anyR n f) = true := (ss_bIf _ _ _).symm.trans h
    by_cases hf : f n = true
    · exact ⟨n, by omega, hf⟩
    · rw [if_neg hf] at h'
      obtain ⟨i, hi, h⟩ := ih h'
      exact ⟨i, by omega, h⟩

theorem ss_lane (c i : ℕ) : lane c i = c / 2 ^ (7 * i) % 128 := by
  change (c >>> (7 * i)) &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem ss_step (c m : ℕ) :
    Nat.lor (c % 2 ^ (7 * m)) (Nat.shiftLeft (lane c m) (7 * m)) = c % 2 ^ (7 * (m + 1)) := by
  change (c % 2 ^ (7 * m)) ||| (lane c m <<< (7 * m)) = _
  have e : 7 * (m + 1) = 7 * m + 7 := by omega
  have e7 : (2 : ℕ) ^ 7 = 128 := rfl
  rw [Nat.or_comm,← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)),
    Nat.shiftLeft_eq, ss_lane, e, Nat.pow_add, Nat.mod_mul, e7, Nat.mul_comm (2 ^ (7 * m)),
    Nat.add_comm (c % 2 ^ (7 * m))]

theorem ss_cand3 : ∀ l < 128, l.testBit 3 = false → l.testBit 5 = false →
    ∃ v < candN 3, cand 3 v = l := by decide +kernel

theorem ss_cand4 : ∀ l < 128, l.testBit 4 = false → l.testBit 6 = false →
    ∃ v < candN 4, cand 4 v = l := by decide +kernel

theorem ss_cand5 : ∀ l < 128, l.testBit 3 = false → l.testBit 5 = false →
    ∃ v < candN 5, cand 5 v = l := by decide +kernel

theorem ss_cand6 : ∀ l < 128, l.testBit 4 = false → l.testBit 6 = false →
    ∃ v < candN 6, cand 6 v = l := by decide +kernel

theorem ss_cand {c m : ℕ} (hm : m < 7) (h0 : lane c 0 = 3) (h1 : lane c 1 = 2)
    (h2 : lane c 2 < 8)
    (h35 : ∀ m, (m = 3 ∨ m = 5) → (lane c m).testBit 3 = false ∧ (lane c m).testBit 5 = false)
    (h46 : ∀ m, (m = 4 ∨ m = 6) → (lane c m).testBit 4 = false ∧ (lane c m).testBit 6 = false) :
    ∃ v < candN m, cand m v = lane c m := by
  have hl : lane c m < 128 := by rw [ss_lane]; exact Nat.mod_lt _ (by norm_num)
  interval_cases m
  · exact ⟨0, by decide, by rw [h0]; rfl⟩
  · exact ⟨0, by decide, by rw [h1]; rfl⟩
  · exact ⟨lane c 2, h2, rfl⟩
  · obtain ⟨a, b⟩ := h35 3 (Or.inl rfl); exact ss_cand3 _ hl a b
  · obtain ⟨a, b⟩ := h46 4 (Or.inl rfl); exact ss_cand4 _ hl a b
  · obtain ⟨a, b⟩ := h35 5 (Or.inr rfl); exact ss_cand5 _ hl a b
  · obtain ⟨a, b⟩ := h46 6 (Or.inr rfl); exact ss_cand6 _ hl a b

noncomputable def ssG (tab d : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => goal2 tab c)
    (fun _ ih m c => lvl true tab ih m c) d

theorem ssG_succ (tab d : ℕ) : ssG tab (d + 1) = lvl true tab (ssG tab d) := rfl

theorem ss_level {tab c : Nat} (hc : c < 2 ^ 49)
    (h0 : lane c 0 = 3) (h1 : lane c 1 = 2) (h2 : lane c 2 < 8)
    (h35 : ∀ m, (m = 3 ∨ m = 5) → (lane c m).testBit 3 = false ∧ (lane c m).testBit 5 = false)
    (h46 : ∀ m, (m = 4 ∨ m = 6) → (lane c m).testBit 4 = false ∧ (lane c m).testBit 6 = false)
    (hst : ∀ m < 7, stage2 true tab (m + 1) (c % 2 ^ (7 * (m + 1))) = true) :
    ∀ d m, m + d = 7 → ssG tab d m (c % 2 ^ (7 * m)) = true → ∃ k < 128, goalK2 tab c k := by
  intro d
  induction d with
  | zero =>
    intro m hm h
    obtain rfl : m = 7 := by omega
    change goal2 tab (c % 2 ^ 49) = true at h
    rw [Nat.mod_eq_of_lt hc] at h
    unfold goal2 at h
    simp only [ss_bIf] at h
    split_ifs at h with h32 h96 h104
    · exact ⟨32, by norm_num, h32⟩
    · exact ⟨96, by norm_num, h96⟩
    · exact ⟨104, by norm_num, h104⟩
    · obtain ⟨k, hk, hg⟩ := ss_anyR h
      exact ⟨k, hk, hg⟩
  | succ d ih =>
    intro m hm h
    have hm7 : m < 7 := by omega
    rw [ssG_succ] at h
    unfold lvl at h
    rw [ss_bIf] at h
    split_ifs at h with hcut
    · rw [cy_bAndD, Bool.and_eq_true] at hcut
      obtain ⟨hm6, hg⟩ := hcut
      have e6 : m = 6 := Nat.eq_of_beq_eq_true hm6
      subst e6
      refine ⟨32, by norm_num, ?_⟩
      have e : beta2 tab c 32 = beta2 tab (c % 2 ^ (7 * 6)) 32 := by
        change bm2 tab 0 (lane c 5) = bm2 tab 0 (lane (c % 2 ^ (7 * 6)) 5)
        have e42 : 2 ^ (7 * 6) = 2 ^ (7 * 5) * 128 := by norm_num
        rw [ss_lane, ss_lane, e42, Nat.mod_mul_right_div_self, Nat.mod_mod]
      unfold goalK2
      rw [e]
      exact hg
    · obtain ⟨v, hv, hcv⟩ := ss_cand hm7 h0 h1 h2 h35 h46
      have hv' := ss_allR h v hv
      have hv'' : bIf(stage2 true tab (m + 1) (c % 2 ^ (7 * (m + 1))),
          ssG tab d (m + 1) (c % 2 ^ (7 * (m + 1))), true) = true := by
        rw [← ss_step c m, ← hcv]
        exact hv'
      rw [ss_bIf, if_pos (hst m hm7)] at hv''
      exact ih (m + 1) (by omega) hv''

public section

theorem srch3_sound {tab c : Nat} (hs : srch3 tab = true) (hc : c < 2 ^ 49)
    (h0 : lane c 0 = 3) (h1 : lane c 1 = 2) (h2 : lane c 2 < 8)
    (h35 : ∀ m, (m = 3 ∨ m = 5) → (lane c m).testBit 3 = false ∧ (lane c m).testBit 5 = false)
    (h46 : ∀ m, (m = 4 ∨ m = 6) → (lane c m).testBit 4 = false ∧ (lane c m).testBit 6 = false)
    (hst : ∀ m < 7, stage2 true tab (m + 1) (c % 2 ^ (7 * (m + 1))) = true) :
    ∃ k < 128, goalK2 tab c k = true := by
  have h7 : ssG tab 7 0 (c % 2 ^ (7 * 0)) = true := by
    have e0 : c % 2 ^ (7 * 0) = 0 := Nat.mod_one c
    rw [e0]
    exact hs
  exact ss_level hc h0 h1 h2 h35 h46 hst 7 0 (by norm_num) h7

end

end CFSG.KC.OmegaCY
