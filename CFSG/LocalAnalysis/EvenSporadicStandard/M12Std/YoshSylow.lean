module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Subgroup

theorem factorization_two_pow_mul_odd {k m : ℕ} (hm : Odd m) :
    (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by
      intro h
      have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hm0).mp h
      have h2 : 2 ∣ m := h
      exact absurd (even_iff_two_dvd.2 h2) (Nat.not_even_iff_odd.2 hm)), add_zero]

theorem no_order_eight_of_sylow {C : Type*} [Group C] [Finite C] {k m : ℕ} (hm : Odd m)
    (hC : Nat.card C = 2 ^ k * m) (P Q : Subgroup C) (hP : ∀ y ∈ P, y ^ 4 = 1)
    (hPcard : 2 ^ k ≤ Nat.card P) (hQcard : Nat.card Q = 2 ^ k) {y₀ : C} (hy₀Q : y₀ ∈ Q)
    (hy₀ : y₀ ^ 4 ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPp : IsPGroup 2 P := fun g => ⟨2, by
    apply Subtype.ext
    simpa using hP g g.2⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hPp
  have hdvd : Nat.card P ∣ Nat.card C := Subgroup.card_subgroup_dvd_card P
  rw [ha, hC] at hdvd
  have hak : a ≤ k := by
    have h1 : 2 ^ a ∣ 2 ^ k * m := hdvd
    by_contra hlt
    have hlt' : k + 1 ≤ a := not_le.1 hlt
    have h2 : 2 ^ (k + 1) ∣ 2 ^ k * m := (pow_dvd_pow 2 hlt').trans h1
    rw [pow_succ] at h2
    have h3 : 2 ∣ m := (Nat.mul_dvd_mul_iff_left (by positivity)).1 h2
    exact absurd (even_iff_two_dvd.2 h3) (Nat.not_even_iff_odd.2 hm)
  have hka : k ≤ a := by
    rw [ha] at hPcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hPcard
  have hPk : Nat.card P = 2 ^ k := by rw [ha, le_antisymm hak hka]
  have hfac : 2 ^ (Nat.card C).factorization 2 = 2 ^ k := by
    rw [hC, factorization_two_pow_mul_odd hm]
  let SP : Sylow 2 C := Sylow.ofCard P (by rw [hPk, hfac])
  let SQ : Sylow 2 C := Sylow.ofCard Q (by rw [hQcard, hfac])
  let φ : SP ≃* SQ := Sylow.equiv SP SQ
  obtain ⟨z, hz⟩ := φ.surjective ⟨y₀, hy₀Q⟩
  have hz4 : (z : C) ^ 4 = 1 := hP z z.2
  apply hy₀
  have h4 : z ^ 4 = 1 := Subtype.ext (by simpa using hz4)
  have := congrArg φ h4
  rw [map_pow, hz, map_one] at this
  simpa using congrArg Subtype.val this

end CFSG.EvenSporadicStandard.M12Std.Yosh
