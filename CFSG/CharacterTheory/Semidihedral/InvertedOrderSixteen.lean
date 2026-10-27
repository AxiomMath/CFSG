module

public import CFSG.CharacterTheory.Semidihedral.ElementOrders

public section

namespace CFSG.Semidihedral

open CFSG.Open

theorem exists_inverted_order_sixteen {n : ℕ} (hn : 5 ≤ n)
    (a : CFSG.Open.SemidihedralGroup n) (ha : orderOf a = 2) (haz : a ≠ CFSG.Semidihedral.z n) :
    ∃ ρ : CFSG.Open.SemidihedralGroup n,
      (a * ρ * a⁻¹ * ρ = 1 ∨ a * ρ * a⁻¹ * ρ = CFSG.Semidihedral.z n) ∧
      ρ ^ 8 = CFSG.Semidihedral.z n ∧ orderOf (ρ ^ 4) = 4 := by
  rcases (involution_iff n (by omega) a).mp ha with h | ⟨j, rfl⟩
  · exact absurd h haz
  have har : r n ^ (2 * j.val) * s n * r n * (r n ^ (2 * j.val) * s n)⁻¹ =
      r n ^ (2 ^ (n - 2) - 1) := by
    calc r n ^ (2 * j.val) * s n * r n * (r n ^ (2 * j.val) * s n)⁻¹
        = r n ^ (2 * j.val) * (s n * r n * (s n)⁻¹) * (r n ^ (2 * j.val))⁻¹ := by group
      _ = r n ^ (2 * j.val) * r n ^ (2 ^ (n - 2) - 1) * (r n ^ (2 * j.val))⁻¹ := by
          rw [s_conj_r]
      _ = r n ^ (2 ^ (n - 2) - 1) := by
          rw [(Commute.pow_pow_self (r n) (2 * j.val) (2 ^ (n - 2) - 1)).eq,
            mul_inv_cancel_right]
  have hr : orderOf (r n) = 2 ^ (n - 1) := orderOf_r n (by omega)
  have hz : z n = r n ^ 2 ^ (n - 2) := rfl
  refine ⟨r n ^ 2 ^ (n - 5), ?_, ?_, ?_⟩
  ·
    have h1 : r n ^ (2 * j.val) * s n * r n ^ 2 ^ (n - 5) * (r n ^ (2 * j.val) * s n)⁻¹ *
        r n ^ 2 ^ (n - 5) = r n ^ (2 ^ (n - 2) * 2 ^ (n - 5)) := by
      rw [← conj_pow, har, ← pow_mul, ← pow_add]
      congr 1
      have hpos : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hpos)]
    rw [h1]
    rcases Nat.lt_or_ge n 6 with h5 | h6
    · right
      obtain rfl : n = 5 := by omega
      rfl
    · left
      rw [← orderOf_dvd_iff_pow_eq_one, hr, ← pow_add]
      exact pow_dvd_pow 2 (by omega)
  · rw [hz, ← pow_mul, show 2 ^ (n - 5) * 8 = 2 ^ (n - 2) by
      rw [show 8 = 2 ^ 3 from rfl, ← pow_add]
      congr 1
      omega]
  · rw [← pow_mul, show 2 ^ (n - 5) * 4 = 2 ^ (n - 3) by
      rw [show 4 = 2 ^ 2 from rfl, ← pow_add]
      congr 1
      omega]
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hr ▸ pow_dvd_pow 2 (by omega)), hr,
      Nat.pow_div (by omega) two_pos, show n - 1 - (n - 3) = 2 by omega]
    rfl

end CFSG.Semidihedral
