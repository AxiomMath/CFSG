module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12Def
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem aor_l12_zpowers_four {G : Type} [Group G] {u v : G} (hu : orderOf u = 4)
    (hv : v ∈ Subgroup.zpowers u) (hv4 : orderOf v = 4) : v = u ∨ v = u⁻¹ := by
  classical
  have hu4 : u ^ 4 = 1 := by simpa [hu] using pow_orderOf_eq_one u
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, hu4⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf] at hv
  obtain ⟨i, hi, hvi⟩ := Finset.mem_image.mp hv
  rw [Finset.mem_range, hu] at hi
  rw [← hvi] at hv4
  interval_cases i
  · exfalso
    rw [pow_zero, orderOf_one] at hv4
    omega
  · left
    rw [← hvi, pow_one]
  · exfalso
    have hle : orderOf (u ^ 2) ≤ 2 :=
      orderOf_le_of_pow_eq_one (by norm_num) (by rw [← pow_mul]; exact hu4)
    omega
  · right
    rw [← hvi]
    exact (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hu4)).symm

namespace L12Coord

variable {S : Type} [Group S] {t u : S}

private theorem aor_pow_mod_two {a : S} (ha : a ^ 2 = 1) (n : ℕ) : a ^ n = a ^ (n % 2) := by
  conv_lhs => rw [← Nat.div_add_mod n 2]
  rw [pow_add, pow_mul, ha, one_pow, one_mul]

private theorem aor_u_pow_mod (h : L12Coord S t u) (n : ℕ) : u ^ n = u ^ (n % 4) := by
  rw [← pow_mod_orderOf u n, h.ord_u]

private theorem aor_t_pow_mod (h : L12Coord S t u) (n : ℕ) : t ^ n = t ^ (n % 2) := by
  rw [← pow_mod_orderOf t n, h.ord_t]

private theorem aor_coord_mul (h : L12Coord S t u) (i j k l : ℕ) :
    (u ^ i * t ^ j) * (u ^ k * t ^ l) = u ^ (i + k) * t ^ (j + l) := by
  have hu : Commute u t := h.comm
  calc (u ^ i * t ^ j) * (u ^ k * t ^ l)
      = u ^ i * (t ^ j * (u ^ k * t ^ l)) := by
          rw [mul_assoc (u ^ i) (t ^ j) (u ^ k * t ^ l)]
    _ = u ^ i * ((t ^ j * u ^ k) * t ^ l) := by rw [← mul_assoc (t ^ j) (u ^ k) (t ^ l)]
    _ = u ^ i * ((u ^ k * t ^ j) * t ^ l) := by rw [(hu.symm.pow_pow j k).eq]
    _ = u ^ i * (u ^ k * (t ^ j * t ^ l)) := by rw [mul_assoc (u ^ k) (t ^ j) (t ^ l)]
    _ = (u ^ i * u ^ k) * (t ^ j * t ^ l) := by
          rw [← mul_assoc (u ^ i) (u ^ k) (t ^ j * t ^ l)]
    _ = u ^ (i + k) * t ^ (j + l) := by rw [← pow_add u i k, ← pow_add t j l]

private theorem aor_coord_sq (h : L12Coord S t u) (i j : ℕ) :
    (u ^ i * t ^ j) ^ 2 = u ^ (2 * i) * t ^ (2 * j) := by
  rw [pow_two, aor_coord_mul h i j i j, ← two_mul i, ← two_mul j]

theorem t_sq (h : L12Coord S t u) : t ^ 2 = 1 := by
  simpa [h.ord_t] using pow_orderOf_eq_one t

theorem t_inv (h : L12Coord S t u) : t⁻¹ = t := by
  exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact t_sq h)

theorem u_pow_four (h : L12Coord S t u) : u ^ 4 = 1 := by
  simpa [h.ord_u] using pow_orderOf_eq_one u

theorem z_sq (h : L12Coord S t u) : (u ^ 2) ^ 2 = 1 := by
  rw [← pow_mul]
  exact u_pow_four h

theorem z_ne_one (h : L12Coord S t u) : u ^ 2 ≠ 1 := by
  intro h2
  have hd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [h.ord_u] at hd
  norm_num at hd

theorem t_ne_one (h : L12Coord S t u) : t ≠ 1 := by
  intro ht
  have h2 := h.ord_t
  rw [ht, orderOf_one] at h2
  omega

theorem t_ne_z (h : L12Coord S t u) : t ≠ u ^ 2 := by
  intro ht
  apply h.not_mem
  rw [ht]
  exact Subgroup.npow_mem_zpowers u 2

private theorem aor_t_two_mul_eq_one (h : L12Coord S t u) (j : ℕ) : t ^ (2 * j) = 1 := by
  rw [pow_mul, t_sq h, one_pow]

private theorem aor_u_sq_pow (h : L12Coord S t u) (i : ℕ) :
    u ^ (2 * i) = 1 ∨ u ^ (2 * i) = u ^ 2 := by
  rw [pow_mul, aor_pow_mod_two (z_sq h) i]
  have hi : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases i % 2 <;> simp

theorem R_comm (h : L12Coord S t u) {x y : S} (hx : x * t = t * x) (hy : y * t = t * y) :
    x * y = y * x := by
  obtain ⟨i, j, rfl⟩ := h.cent x hx
  obtain ⟨k, l, rfl⟩ := h.cent y hy
  rw [aor_coord_mul h i j k l, aor_coord_mul h k l i j, Nat.add_comm i k, Nat.add_comm j l]

theorem R_sq (h : L12Coord S t u) {x : S} (hx : x * t = t * x) : x ^ 2 = 1 ∨ x ^ 2 = u ^ 2 := by
  obtain ⟨i, j, rfl⟩ := h.cent x hx
  rw [aor_coord_sq h i j, aor_t_two_mul_eq_one h j, mul_one]
  exact aor_u_sq_pow h i

theorem R_inv (h : L12Coord S t u) {x : S} (hx : x * t = t * x) (hx2 : x ^ 2 = 1) :
    x = 1 ∨ x = u ^ 2 ∨ x = t ∨ x = u ^ 2 * t := by
  obtain ⟨i, j, rfl⟩ := h.cent x hx
  have hsq : u ^ (2 * i) = 1 := by
    rw [aor_coord_sq h i j, aor_t_two_mul_eq_one h j, mul_one] at hx2
    exact hx2
  have hi : i % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
    · exact h0
    · exfalso
      have hu2 : (u ^ 2) ^ i = 1 := by rw [← pow_mul]; exact hsq
      rw [aor_pow_mod_two (z_sq h) i, h1, pow_one] at hu2
      exact z_ne_one h hu2
  obtain ⟨k, hk⟩ := Nat.dvd_iff_mod_eq_zero.mpr hi
  rw [hk, pow_mul u 2 k, aor_pow_mod_two (z_sq h) k, aor_pow_mod_two (t_sq h) j]
  have hk2 : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hj2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases k % 2 <;> interval_cases j % 2 <;> simp

theorem R_gen (h : L12Coord S t u) {v : S} (hv : v * t = t * v) (hv4 : orderOf v = 4)
    (hne : v ∉ Subgroup.zpowers u) {x : S} (hx : x * t = t * x) :
    ∃ i j : ℕ, x = u ^ i * v ^ j := by
  obtain ⟨i, j, hvij⟩ := h.cent v hv
  rw [aor_u_pow_mod h i, aor_t_pow_mod h j] at hvij
  have hj : j % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
    · exfalso
      apply hne
      rw [hvij, h0, pow_zero, mul_one]
      exact Subgroup.npow_mem_zpowers u (i % 4)
    · exact h1
  rw [hj, pow_one] at hvij
  have ha : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have ht : t = u ^ (4 - i % 4) * v := by
    rw [hvij, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt ha), u_pow_four h, one_mul]
  obtain ⟨m, n, hxmn⟩ := h.cent x hx
  rw [aor_u_pow_mod h m, aor_t_pow_mod h n] at hxmn
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
  · refine ⟨m % 4, 0, ?_⟩
    rw [hxmn, hn0]
    simp
  · refine ⟨m % 4 + (4 - i % 4), 1, ?_⟩
    rw [hxmn, hn1, pow_one, ht, ← mul_assoc, ← pow_add]
    simp

end L12Coord

end CFSG.OddStandard.SmallF3.Omega
