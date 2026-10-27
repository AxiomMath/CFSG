module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisPhan

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LocalAnalysis.ComponentInitial

@[expose] def HeisB12AtCard (q : ℕ) : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → ℓ ^ f = q →
    ∀ ω : K, IsPrimitiveRoot ω 3 → heisB12 ℓ f K ≤ heisClosure ℓ f K ω

theorem pow_ne_fourteen {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) : ℓ ^ f ≠ 14 := by
  intro h14
  have hf0 : f ≠ 0 := by omega
  have hℓ14 : ℓ ∣ 2 * 7 := by
    rw [show 2 * 7 = ℓ ^ f by omega]
    exact dvd_pow_self ℓ hf0
  rcases (Nat.Prime.dvd_mul hℓ).1 hℓ14 with h2 | h7
  · have : ℓ = 2 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2
    subst this
    have h72 : 7 ∣ 2 ^ f := by rw [h14]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h72
    omega
  · have : ℓ = 7 := (Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 h7
    subst this
    have h27 : 2 ∣ 7 ^ f := by rw [h14]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h27
    omega

theorem unitaryHeisCore_of_finite_cases (h5 : HeisB12AtCard 5)
    (h8 : HeisB12AtCard 8) (h11 : HeisB12AtCard 11) : UnitaryHeisCore := by
  intro ℓ f K _ h hq3 hq ω hω
  have hf := h.one_le
  have hpow : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by omega : f ≠ 0) h.prime.one_lt
    omega
  have h14 := pow_ne_fourteen h.prime hf
  have hcases : ℓ ^ f = 5 ∨ ℓ ^ f = 8 ∨ ℓ ^ f = 11 ∨ 17 ≤ ℓ ^ f := by omega
  have hB : heisB12 ℓ f K ≤ heisClosure ℓ f K ω := by
    rcases hcases with h5' | h8' | h11' | h17
    · exact h5 ℓ f K h h5' ω hω
    · exact h8 ℓ f K h h8' ω hω
    · exact h11 ℓ f K h h11' ω hω
    · exact heisB12_le_heisClosure_of_large h hq3 h17 hω
  exact eq_top_of_heisB12_le h hq hB

end CFSG.LieType.SeitzGeneration
