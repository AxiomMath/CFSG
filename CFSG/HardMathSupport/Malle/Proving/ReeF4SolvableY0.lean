module

public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.HardMathSupport.Malle.Proving

theorem isSolvable_of_card_dvd {G : Type*} [Group G] [Finite G]
    (h : Nat.card G ∣ 2 ^ 5 * 3) : Group.IsSolvable G := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.mp h
  obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hk₁
  have hb : ∃ b : ℕ, Nat.card G = 2 ^ a * 3 ^ b := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hk₂ with rfl | rfl
    · exact ⟨0, by rw [← hk]; simp⟩
    · exact ⟨1, by rw [← hk]; simp⟩
  obtain ⟨b, hb⟩ := hb
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hb])

variable {Y : Type} [Group Y] [Finite Y]

end CFSG.HardMathSupport.Malle.Proving
