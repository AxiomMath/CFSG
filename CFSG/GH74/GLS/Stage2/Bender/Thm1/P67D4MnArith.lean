module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem not_dvd_index_minus (q i : ℕ) (hq : q % 3 = 2) (hq1 : 1 < q)
    (h : i * (3 * ((q + 1) * (q ^ 3 + 1))) =
      q ^ 12 * (q ^ 2 - 1) * (q ^ 6 - 1) * (q ^ 8 + q ^ 4 + 1)) : ¬ 3 ∣ i := by
  have key : ∀ a u B A P s R : ℕ, 0 < B → 0 < A →
      i * (3 * (B * A)) = a * (u * B) * (u * P * A) * (P * (3 * s) * R) →
      i = a * u * u * P * P * s * R := by
    intro a u B A P s R hB hA hE
    have hpos : 0 < 3 * (B * A) := by positivity
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc 3 * (B * A) * i = i * (3 * (B * A)) := by ring
      _ = _ := hE
      _ = _ := by ring
  obtain ⟨m, rfl⟩ : ∃ m, q = 3 * m + 2 := ⟨q / 3, by omega⟩
  have e2 : (3 * m + 2) ^ 2 - 1 = (3 * m + 1) * (3 * m + 2 + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have e6 : (3 * m + 2) ^ 6 - 1 =
      (3 * m + 1) * (9 * m ^ 2 + 15 * m + 7) * ((3 * m + 2) ^ 3 + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  have e8 : (3 * m + 2) ^ 8 + (3 * m + 2) ^ 4 + 1 =
      (9 * m ^ 2 + 15 * m + 7) * (3 * (3 * m ^ 2 + 3 * m + 1)) *
        (81 * m ^ 4 + 216 * m ^ 3 + 207 * m ^ 2 + 84 * m + 13) := by
    ring
  rw [e2, e6, e8] at h
  have h3 := key _ _ _ _ _ _ _ (by omega) (by positivity) h
  have hi : i % 3 = 1 := by
    rw [h3]
    simp [Nat.mul_mod, Nat.pow_mod, Nat.add_mod]
  omega

end CFSG.GH74.GLS.Stage2.Bender.Thm1
