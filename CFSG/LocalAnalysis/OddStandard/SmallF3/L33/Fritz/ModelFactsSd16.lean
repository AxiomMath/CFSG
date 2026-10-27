module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.L33

theorem sd16_involution_isConj {G : Type*} [Group G] {x y : G} (hx : x ^ 8 = 1) (hx4 : x ^ 4 ≠ 1)
    (hy : y ^ 2 = 1) (hyx : y * x * y⁻¹ = x ^ 3) {w : G}
    (hw : w ∈ Subgroup.closure ({x, y} : Set G)) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1) :
    IsConj w (x ^ 4) ∨ IsConj w y := by
  have hxord : orderOf x = 8 := by
    have hdv : orderOf x ∣ 8 := orderOf_dvd_of_pow_eq_one hx
    have hnd : ¬ orderOf x ∣ 4 := fun h => hx4 (orderOf_dvd_iff_pow_eq_one.mp h)
    have hpos : 0 < orderOf x := Nat.pos_of_dvd_of_pos hdv (by norm_num)
    have hle : orderOf x ≤ 8 := Nat.le_of_dvd (by norm_num) hdv
    interval_cases orderOf x <;> simp_all
  have hyxp : ∀ n : ℕ, y * x ^ n * y⁻¹ = x ^ (3 * n) := by
    intro n
    have h := conj_pow (i := n) (a := y) (b := x)
    rw [hyx, ← pow_mul] at h
    exact h.symm
  have hyxi : ∀ n : ℕ, y * x ^ n = x ^ (3 * n) * y := by
    intro n
    rw [← hyxp n]
    group
  have hyxpow : ∀ j k : ℕ, y ^ j * x ^ k = x ^ (3 ^ j * k) * y ^ j := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
        intro k
        calc y ^ (j + 1) * x ^ k
            = y * (y ^ j * x ^ k) := by rw [pow_succ']; group
          _ = y * (x ^ (3 ^ j * k) * y ^ j) := by rw [ih k]
          _ = (y * x ^ (3 ^ j * k) * y⁻¹) * y ^ (j + 1) := by group
          _ = x ^ (3 * (3 ^ j * k)) * y ^ (j + 1) := by rw [hyxp (3 ^ j * k)]
          _ = x ^ (3 ^ (j + 1) * k) * y ^ (j + 1) := by
                rw [show 3 * (3 ^ j * k) = 3 ^ (j + 1) * k by rw [pow_succ]; ring]
  have hmul : ∀ (u v : G) (i j k l : ℕ), u = x ^ i * y ^ j → v = x ^ k * y ^ l →
      ∃ a b : ℕ, u * v = x ^ a * y ^ b := by
    intro u v i j k l hu hv
    refine ⟨i + 3 ^ j * k, j + l, ?_⟩
    rw [hu, hv]
    calc (x ^ i * y ^ j) * (x ^ k * y ^ l)
        = x ^ i * (y ^ j * x ^ k) * y ^ l := by group
      _ = x ^ i * (x ^ (3 ^ j * k) * y ^ j) * y ^ l := by rw [hyxpow j k]
      _ = x ^ i * x ^ (3 ^ j * k) * (y ^ j * y ^ l) := by group
      _ = x ^ (i + 3 ^ j * k) * y ^ (j + l) := by rw [← pow_add, ← pow_add]
  have hmem : ∀ w ∈ Subgroup.closure ({x, y} : Set G), ∃ i j : ℕ, w = x ^ i * y ^ j := by
    intro w hw
    refine Subgroup.closure_induction''
      (p := fun w _ => ∃ i j : ℕ, w = x ^ i * y ^ j) ?_ ?_ ?_ ?_ hw
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · refine ⟨7, 0, ?_⟩
        simp only [pow_zero, mul_one]
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx]
      · refine ⟨0, 1, ?_⟩
        simp only [pow_zero, one_mul, pow_one]
        rw [inv_eq_iff_mul_eq_one, ← pow_two, hy]
    · exact ⟨0, 0, by simp⟩
    · intro u v hu hv ihu ihv
      obtain ⟨i, j, rfl⟩ := ihu
      obtain ⟨k, l, rfl⟩ := ihv
      exact hmul (x ^ i * y ^ j) (x ^ k * y ^ l) i j k l rfl rfl
  obtain ⟨i, j, hwij⟩ := hmem w hw
  rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
  · obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hj0
    have hyj : y ^ j = 1 := by rw [hm, pow_mul, hy, one_pow]
    have hw_eq : x ^ i * y ^ j = x ^ i := by rw [hyj, mul_one]
    rw [hwij, hw_eq, ← pow_mul] at hw2
    have hx2i : x ^ (2 * i) = 1 := by
      rw [mul_comm i 2] at hw2
      exact hw2
    have hdvd : 8 ∣ 2 * i := by
      rw [← hxord]
      exact orderOf_dvd_of_pow_eq_one hx2i
    obtain ⟨t, ht⟩ := hdvd
    have hi : i = 4 * t := by omega
    have htodd : ¬ 2 ∣ t := by
      rintro ⟨s, hs⟩
      apply hw1
      rw [hwij, hw_eq, hi, hs]
      rw [show 4 * (2 * s) = 8 * s by ring, pow_mul, hx, one_pow]
    have htmod : t % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one t with h | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h) htodd
      · exact h
    obtain ⟨s, hs⟩ : ∃ s, t = 2 * s + 1 := ⟨t / 2, by omega⟩
    have hxi : x ^ i = x ^ 4 := by
      rw [hi, hs, show 4 * (2 * s + 1) = 8 * s + 4 by ring, pow_add, pow_mul, hx,
        one_pow, one_mul]
    left
    rw [hwij, hw_eq, hxi]
  · obtain ⟨m, hm⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
    have hyj : y ^ j = y := by rw [hm, pow_succ', pow_mul, hy, one_pow, mul_one]
    have hw_eq : x ^ i * y ^ j = x ^ i * y := by rw [hyj]
    rw [hwij, hw_eq] at hw2
    have hsq : (x ^ i * y) ^ 2 = x ^ (4 * i) := by
      calc (x ^ i * y) ^ 2 = x ^ i * (y * x ^ i) * y := by rw [pow_two]; group
        _ = x ^ i * (x ^ (3 * i) * y) * y := by rw [hyxi i]
        _ = x ^ i * x ^ (3 * i) * (y * y) := by group
        _ = x ^ (i + 3 * i) * (y * y) := by rw [← pow_add]
        _ = x ^ (4 * i) := by
              rw [← pow_two, hy, mul_one]
              congr 1
              ring
    have hx4i : x ^ (4 * i) = 1 := by rw [← hsq]; exact hw2
    have hdvd : 8 ∣ 4 * i := by
      rw [← hxord]
      exact orderOf_dvd_of_pow_eq_one hx4i
    obtain ⟨t, ht⟩ := hdvd
    have hi : i = 2 * t := by omega
    have hconj : x ^ (t % 4) * (x ^ (2 * t) * y) * (x ^ (t % 4))⁻¹ = y := by
      have hinv : (x ^ (t % 4))⁻¹ = x ^ (8 - t % 4) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, show t % 4 + (8 - t % 4) = 8 by omega, hx]
      calc x ^ (t % 4) * (x ^ (2 * t) * y) * (x ^ (t % 4))⁻¹
          = x ^ (t % 4) * (x ^ (2 * t) * y) * x ^ (8 - t % 4) := by rw [hinv]
        _ = x ^ (t % 4) * x ^ (2 * t) * (y * x ^ (8 - t % 4)) := by group
        _ = x ^ (t % 4) * x ^ (2 * t) * (x ^ (3 * (8 - t % 4)) * y) := by
              rw [hyxi (8 - t % 4)]
        _ = x ^ (t % 4 + 2 * t + 3 * (8 - t % 4)) * y := by
              rw [← mul_assoc, ← pow_add, ← pow_add]
        _ = y := by
              rw [show t % 4 + 2 * t + 3 * (8 - t % 4) = 8 * (t / 4 + 3) by omega,
                pow_mul, hx, one_pow, one_mul]
    right
    rw [hwij, hw_eq, hi]
    exact isConj_iff.mpr ⟨x ^ (t % 4), hconj⟩

end CFSG.OddStandard.SmallF3.L33
