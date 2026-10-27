module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem isSolvable_of_card_dvd_216 {G : Type*} [Group G] (h : Nat.card G ∣ 216) :
    Group.IsSolvable G := by
  have : Finite G := Nat.finite_of_card_ne_zero (Nat.pos_of_dvd_of_pos h (by norm_num)).ne'
  have h216 : (216 : ℕ) = 2 ^ 3 * 3 ^ 3 := by norm_num
  rw [h216] at h
  obtain ⟨m, k, hm, hk, hmk⟩ := Nat.dvd_mul.1 h
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hm
  obtain ⟨b, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hmk])

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
