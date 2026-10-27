module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cNShape
public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.GH74.GLS.Stage4.Rest CFSG.GH74.GLS.Stage4.Rest.Mix11cN

section Rot

theorem m3_rot_pow_lt {n j : ℕ} (hj : j + 1 < n) : rot 2 n (2 ^ j) = 2 ^ (j + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : 2 ^ j < 2 ^ m := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  rw [rot_succ_eq (p := 2), Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, add_zero, pow_succ]

theorem m3_rot_pow_last {m : ℕ} : rot 2 (m + 1) (2 ^ m) = 1 := by
  rw [rot_succ_eq (p := 2), Nat.mod_self, Nat.div_self (by positivity)]

theorem m3_iterate_rot_pow {n j : ℕ} (s : ℕ) (h : j + s < n) :
    (rot 2 n)^[s] (2 ^ j) = 2 ^ (j + s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih (by omega), m3_rot_pow_lt (by omega)]
    rfl

theorem m3_exists_rot_one {n j : ℕ} (hj : j < n) : ∃ s, (rot 2 n)^[s] (2 ^ j) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨(m - j) + 1, ?_⟩
  rw [Function.iterate_succ_apply', m3_iterate_rot_pow (m - j) (by omega)]
  have : j + (m - j) = m := by omega
  rw [this, m3_rot_pow_last]

theorem m3_rot_two_lt {r j : ℕ} (hj : j + 1 < r) :
    rot 2 (2 * r) ((1 + 2 ^ r) * 2 ^ j) = (1 + 2 ^ r) * 2 ^ (j + 1) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * r = m + 1 := ⟨2 * r - 1, by omega⟩
  have hc : 2 ^ (j + 1) ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hr : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hm2 : 2 ^ m = 2 ^ r * 2 ^ (r - 1) := by
    rw [← pow_add]; congr 1; omega
  have ha : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hj2 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ']
  have hlt : (1 + 2 ^ r) * 2 ^ j < 2 ^ m := by
    rw [hm2, hr]
    nlinarith
  rw [hm, rot_succ_eq (p := 2), Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, add_zero, pow_succ]
  ring

theorem m3_rot_two_last {r : ℕ} (hr : 0 < r) :
    rot 2 (2 * r) ((1 + 2 ^ r) * 2 ^ (r - 1)) = 1 + 2 ^ r := by
  obtain ⟨m, hm⟩ : ∃ m, 2 * r = m + 1 := ⟨2 * r - 1, by omega⟩
  have hpos : 0 < 2 ^ m := by positivity
  have hlt : 2 ^ (r - 1) < 2 ^ m := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
  have hm2 : 2 ^ m = 2 ^ r * 2 ^ (r - 1) := by
    rw [← pow_add]; congr 1; omega
  have hA : (1 + 2 ^ r) * 2 ^ (r - 1) = 2 ^ (r - 1) + 2 ^ m := by
    rw [hm2]; ring
  have hr2 : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hm, rot_succ_eq (p := 2), hA, Nat.add_mod_right, Nat.mod_eq_of_lt hlt,
    Nat.add_div_right _ hpos, Nat.div_eq_of_lt hlt]
  rw [hr2]
  ring

theorem m3_iterate_rot_two {r j : ℕ} (s : ℕ) (h : j + s < r) :
    (rot 2 (2 * r))^[s] ((1 + 2 ^ r) * 2 ^ j) = (1 + 2 ^ r) * 2 ^ (j + s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih (by omega), m3_rot_two_lt (by omega)]
    rfl

theorem m3_exists_rot_two {r j : ℕ} (hr : 0 < r) (hj : j < r) :
    ∃ s, (rot 2 (2 * r))^[s] ((1 + 2 ^ r) * 2 ^ j) = 1 + 2 ^ r := by
  refine ⟨(r - 1 - j) + 1, ?_⟩
  rw [Function.iterate_succ_apply', m3_iterate_rot_two (r - 1 - j) (by omega)]
  have : j + (r - 1 - j) = r - 1 := by omega
  rw [this, m3_rot_two_last hr]

end Rot

section Shape

theorem m3_shape_one {n A : ℕ} (hA : A < 2 ^ n) (h : ∏ i ∈ Finset.range n, (dg 2 A i + 1) = 2) :
    ∃ j < n, A = 2 ^ j := by
  obtain ⟨j, hj, hj2, hz⟩ := exists_unique_digit Nat.prime_two (fun i => dg 2 A i) h
  refine ⟨j, hj, (sum_dg Nat.one_lt_two hA).trans ?_⟩
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
  · have h2 : dg 2 A j = 1 := by omega
    rw [h2, one_mul]
  · intro i hi hij
    rw [hz i (Finset.mem_range.1 hi) hij]
    simp

theorem m3_shape_two {n r A : ℕ} (hA : A < 2 ^ n) (hn : n = r * 2)
    (hper : ∀ i, dg 2 A ((i + r) % n) = dg 2 A (i % n))
    (h : ∏ i ∈ Finset.range r, (dg 2 A i + 1) = 2) :
    ∃ j < r, A = (1 + 2 ^ r) * 2 ^ j := by
  subst hn
  obtain ⟨j, hj, hj2, hz⟩ := exists_unique_digit Nat.prime_two (fun i => dg 2 A i) h
  refine ⟨j, hj, ?_⟩
  have hf : ∀ i, (fun i => dg 2 A (i % (r * 2))) (i + r) = (fun i => dg 2 A (i % (r * 2))) i :=
    hper
  have h1 : A = ∑ i ∈ Finset.range (r * 2), dg 2 A (i % (r * 2)) * 2 ^ i := by
    refine (sum_dg Nat.one_lt_two hA).trans (Finset.sum_congr rfl fun i hi => ?_)
    rw [Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
  have h2 : ∑ i ∈ Finset.range r, dg 2 A (i % (r * 2)) * 2 ^ i = 2 ^ j := by
    have h3 : ∑ i ∈ Finset.range r, dg 2 A (i % (r * 2)) * 2 ^ i =
        ∑ i ∈ Finset.range r, dg 2 A i * 2 ^ i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hi) (by omega : r ≤ r * 2))]
    rw [h3, Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
    · have h4 : dg 2 A j = 1 := by omega
      rw [h4, one_mul]
    · intro i hi hij
      rw [hz i (Finset.mem_range.1 hi) hij]
      simp
  have h5 := sum_range_period (p := 2) (f := fun i => dg 2 A (i % (r * 2))) (r := r) hf 2
  rw [← h1, h2] at h5
  rw [h5]
  simp [Finset.sum_range_succ]

theorem m3_lt_two_pow {t : ℕ} (ht : 3 ≤ t) : 2 * t < 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem m3_numerics {n A : ℕ} (hn : 0 < n) (hA : A < 2 ^ n) (hA0 : A ≠ 0)
    (hd : rotPeriod 2 n A * digitProd 2 n A ≤ 2 * n) :
    2 * n ≤ rotPeriod 2 n A * digitProd 2 n A ∧
      ((∃ s, (rot 2 n)^[s] A = 1) ∨
        (∃ k, n = 2 * k ∧ 0 < k ∧ ∃ s, (rot 2 n)^[s] A = 1 + 2 ^ k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨r, t, P, hr, hnt, hr0, ht0, hP, hD, hprod⟩ :=
    period_structure Nat.one_lt_two hA hA0
  have hper := dg_period Nat.one_lt_two hA
  rw [hr] at hper
  rw [hr, hD] at hd ⊢
  have h1 : P ^ t ≤ 2 * t := by
    have : r * P ^ t ≤ r * (2 * t) := by
      calc r * P ^ t ≤ 2 * (m + 1) := hd
        _ = r * (2 * t) := by rw [hnt]; ring
    exact Nat.le_of_mul_le_mul_left this hr0
  have h2 : 2 ^ t ≤ 2 * t := (Nat.pow_le_pow_left hP t).trans h1
  have ht : t ≤ 2 := by
    by_contra h
    exact absurd h2 (not_le.mpr (m3_lt_two_pow (by omega)))
  have hP2 : P = 2 := by
    interval_cases t
    · simp at h1; omega
    · nlinarith
  subst hP2
  have ht' : t = 1 ∨ t = 2 := by omega
  rcases ht' with rfl | rfl
  · refine ⟨by rw [hnt]; omega, Or.inl ?_⟩
    have hnr : m + 1 = r := by omega
    rw [← hnr] at hprod
    obtain ⟨j, hj, rfl⟩ := m3_shape_one hA hprod
    exact m3_exists_rot_one hj
  · refine ⟨by rw [hnt]; omega, Or.inr ?_⟩
    obtain ⟨j, hj, rfl⟩ := m3_shape_two hA hnt hper hprod
    refine ⟨r, by omega, hr0, ?_⟩
    have : m + 1 = 2 * r := by omega
    rw [this]
    exact m3_exists_rot_two hr0 hj

theorem m3_two_mul_le {n A : ℕ} (hn : 0 < n) (hA : A < 2 ^ n) (hA0 : A ≠ 0) :
    2 * n ≤ rotPeriod 2 n A * digitProd 2 n A := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨r, t, P, hr, hnt, hr0, ht0, hP, hD, -⟩ := period_structure Nat.one_lt_two hA hA0
  rw [hr, hD, hnt]
  have h1 : 2 * t ≤ P ^ t := (two_mul_le_two_pow ht0).trans (Nat.pow_le_pow_left hP t)
  calc 2 * (r * t) = r * (2 * t) := by ring
    _ ≤ r * P ^ t := Nat.mul_le_mul_left r h1

end Shape

end CFSG.CGT.PushingUpLit.CGT6
