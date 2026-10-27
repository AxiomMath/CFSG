module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GroupTheory

open QuaternionGroup

theorem two_mul_eq_zero_iff_zmod {m : ℕ} [NeZero m] (i : ZMod (2 * m)) :
    2 * i = 0 ↔ i = 0 ∨ i = (m : ZMod (2 * m)) := by
  have : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩
  have hlt : i.val < 2 * m := ZMod.val_lt i
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 2 * m ∧ (n : ZMod (2 * m)) = i :=
    ⟨i.val, hlt, ZMod.natCast_zmod_val i⟩
  have e : (2 : ZMod (2 * m)) * (n : ZMod (2 * m)) = ((2 * n : ℕ) : ZMod (2 * m)) := by
    push_cast
    ring
  rw [e, ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    have hdvd : m ∣ n := Nat.dvd_of_mul_dvd_mul_left two_pos h
    obtain ⟨k, rfl⟩ := hdvd
    have hk2 : k < 2 := by
      by_contra hk2
      push Not at hk2
      have : m * 2 ≤ m * k := Nat.mul_le_mul_left m hk2
      omega
    interval_cases k
    · left
      rw [mul_zero, Nat.cast_zero]
    · right
      rw [mul_one]
  · rintro (h | h)
    · rw [ZMod.natCast_eq_zero_iff] at h
      exact dvd_mul_of_dvd_right h 2
    · have h' : ((n : ℕ) : ZMod (2 * m)) - (m : ℕ) = 0 := by rw [h, sub_self]
      have hmn : m ≤ n ∨ n < m := le_or_gt m n
      rcases hmn with hmn | hmn
      · rw [← Nat.cast_sub hmn, ZMod.natCast_eq_zero_iff] at h'
        have : n - m < 2 * m := by omega
        have h0 : n - m = 0 := Nat.eq_zero_of_dvd_of_lt h' this
        have : n = m := by omega
        rw [this]
      · have h'' : ((m : ℕ) : ZMod (2 * m)) - (n : ℕ) = 0 := by rw [h, sub_self]
        rw [← Nat.cast_sub hmn.le, ZMod.natCast_eq_zero_iff] at h''
        have h0 : m - n = 0 := Nat.eq_zero_of_dvd_of_lt h'' (by omega)
        omega

variable {m : ℕ}

theorem a_mul_xa_eq_xa_mul_a_iff [NeZero m] (i j : ZMod (2 * m)) :
    (a i : QuaternionGroup m) * xa j = xa j * a i ↔ i = 0 ∨ i = (m : ZMod (2 * m)) := by
  rw [a_mul_xa, xa_mul_a, xa.injEq, ← two_mul_eq_zero_iff_zmod]
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

theorem xa_mul_xa_comm_iff [NeZero m] (j l : ZMod (2 * m)) :
    (xa l : QuaternionGroup m) * xa j = xa j * xa l ↔ l = j ∨ l = j + (m : ZMod (2 * m)) := by
  rw [xa_mul_xa, xa_mul_xa, a.injEq]
  have h : ((m : ZMod (2 * m)) + j - l = m + l - j) ↔ 2 * (l - j) = 0 := by
    constructor
    · intro h
      linear_combination -h
    · intro h
      linear_combination -h
  rw [h, two_mul_eq_zero_iff_zmod, sub_eq_zero, sub_eq_iff_eq_add, add_comm (m : ZMod (2 * m))]

theorem a_m_eq_neg [NeZero m] : (-(m : ZMod (2 * m))) = m := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul, two_mul_eq_zero_iff_zmod]
  exact Or.inr rfl

theorem quaternion_centralizers (hm : 2 ≤ m) :
    (∀ i : ZMod (2 * m), i ≠ 0 → i ≠ (m : ZMod (2 * m)) → ∀ g : QuaternionGroup m,
      g ∈ Subgroup.centralizer {a i} ↔ ∃ k, g = a k) ∧
    (∀ (j : ZMod (2 * m)) (g : QuaternionGroup m),
      (g ∈ Subgroup.centralizer {xa j} ↔ g ∈ Subgroup.zpowers (xa j)) ∧
      (g ∈ Subgroup.zpowers (xa j) ↔
        g = a 0 ∨ g = a (m : ZMod (2 * m)) ∨ g = xa j ∨ g = xa (j + (m : ZMod (2 * m))))) ∧
    (∀ g : QuaternionGroup m, g ∈ Subgroup.center (QuaternionGroup m) ↔
      g = a 0 ∨ g = a (m : ZMod (2 * m))) ∧
    ∀ H : Subgroup (QuaternionGroup m), (∀ x ∈ H, ∀ y ∈ H, x * y = y * x) → IsCyclic H := by
  classical
  have : NeZero m := ⟨by omega⟩
  have hcxa : ∀ (j : ZMod (2 * m)) (g : QuaternionGroup m), g ∈ Subgroup.centralizer {xa j} ↔
      g = a 0 ∨ g = a (m : ZMod (2 * m)) ∨ g = xa j ∨ g = xa (j + (m : ZMod (2 * m))) := by
    intro j g
    rw [Subgroup.mem_centralizer_singleton_iff]
    cases g with
    | a k =>
      rw [a_mul_xa_eq_xa_mul_a_iff]
      simp only [a.injEq, reduceCtorEq, or_false]
    | xa k =>
      rw [xa_mul_xa_comm_iff]
      simp only [xa.injEq, reduceCtorEq, false_or]
  have hzxa : ∀ (j : ZMod (2 * m)) (g : QuaternionGroup m), g ∈ Subgroup.zpowers (xa j) ↔
      g = a 0 ∨ g = a (m : ZMod (2 * m)) ∨ g = xa j ∨ g = xa (j + (m : ZMod (2 * m))) := by
    intro j g
    rw [mem_zpowers_iff_mem_range_orderOf, orderOf_xa]
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨n, hn, rfl⟩
      interval_cases n
      · left
        rw [pow_zero, one_def]
      · right; right; left
        rw [pow_one]
      · right; left
        rw [xa_sq]
      · right; right; right
        rw [pow_succ, xa_sq, a_mul_xa, sub_eq_add_neg, a_m_eq_neg]
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, by norm_num, by rw [pow_zero, one_def]⟩
      · exact ⟨2, by norm_num, xa_sq j⟩
      · exact ⟨1, by norm_num, pow_one _⟩
      · exact ⟨3, by norm_num, by rw [pow_succ, xa_sq, a_mul_xa, sub_eq_add_neg, a_m_eq_neg]⟩
  have h1 : (1 : ZMod (2 * m)) ≠ 0 := by
    have : Fact (1 < 2 * m) := ⟨by omega⟩
    exact one_ne_zero
  have h1m : (1 : ZMod (2 * m)) ≠ (m : ZMod (2 * m)) := by
    intro h
    have : NeZero (2 * m) := ⟨by omega⟩
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hv
    have : Fact (1 < 2 * m) := ⟨by omega⟩
    rw [ZMod.val_one] at hv
    omega
  refine ⟨fun i hi0 him g => ?_, fun j g => ⟨by rw [hcxa, hzxa], hzxa j g⟩, fun g => ?_,
    fun H hH => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    cases g with
    | a k =>
      simp only [a_mul_a, add_comm, a.injEq, exists_eq']
    | xa k =>
      have h := a_mul_xa_eq_xa_mul_a_iff i k
      constructor
      · intro hc
        exfalso
        rcases h.1 hc.symm with h0 | h0
        · exact hi0 h0
        · exact him h0
      · rintro ⟨k', hk'⟩
        exact absurd hk' (by simp)
  · rw [Subgroup.mem_center_iff]
    constructor
    · intro hg
      cases g with
      | a k =>
        have := hg (xa 0)
        rw [eq_comm, a_mul_xa_eq_xa_mul_a_iff] at this
        rcases this with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      | xa k =>
        exfalso
        have := hg (a 1)
        rw [a_mul_xa_eq_xa_mul_a_iff] at this
        rcases this with h | h
        · exact h1 h
        · exact h1m h
    · rintro (rfl | rfl) h
      · rw [a_zero, mul_one, one_mul]
      · cases h with
        | a k => rw [a_mul_a, a_mul_a, add_comm]
        | xa k =>
          exact ((a_mul_xa_eq_xa_mul_a_iff _ k).2 (Or.inr rfl)).symm
  ·
    by_cases hA : ∃ j, xa j ∈ H
    · obtain ⟨j, hj⟩ := hA
      have hle : H ≤ Subgroup.zpowers (xa j) := by
        intro g hg
        rw [hzxa, ← hcxa, Subgroup.mem_centralizer_singleton_iff]
        exact (hH _ hj _ hg).symm
      exact Subgroup.isCyclic_of_le hle
    · push Not at hA
      have hle : H ≤ Subgroup.zpowers (a 1 : QuaternionGroup m) := by
        intro g hg
        cases g with
        | a k =>
          have : NeZero (2 * m) := ⟨by omega⟩
          refine ⟨(k.val : ℤ), ?_⟩
          simp only [zpow_natCast, a_one_pow, ZMod.natCast_zmod_val]
        | xa k => exact absurd hg (hA k)
      exact Subgroup.isCyclic_of_le hle

end CFSG.GroupTheory
