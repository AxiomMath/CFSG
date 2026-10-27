module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.FrobeniusBlockStability

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem exists_lyons_galois_perm (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (h2 : 2 ∣ Nat.card G)
    (h5 : 5 ∣ Nat.card G) :
    ∃ (k : ℕ) (τ : Equiv.Perm basis.index), k % 2 = 1 ∧ k % 5 = 2 ∧
      (∀ a g, (basis.representation (τ a)).character g =
        (basis.representation a).character (g ^ k)) ∧
      (∀ a, Module.finrank ℂ (basis.representation (τ a)).vector =
        Module.finrank ℂ (basis.representation a).vector) ∧
      (∀ a b, (basis.representation a).character = 1 →
        (τ b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) a ↔
          b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) a)) ∧
      (∀ a (g : G) (j : ℕ), g ^ (2 ^ j) = 1 →
        (basis.representation (τ a)).character g = (basis.representation a).character g) := by
  obtain ⟨e, M, hModd, hN⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.card_pos (α := G)).ne'
  have hM : 0 < M := hModd.pos
  have hpM : ¬ 2 ∣ M := fun h => (Nat.not_even_iff_odd.mpr hModd) (even_iff_two_dvd.mpr h)
  have he : 1 ≤ e := by
    by_contra he
    have he0 : e = 0 := by omega
    rw [he0, pow_zero, one_mul] at hN
    exact hpM (hN ▸ h2)
  have h5M : 5 ∣ M := by
    have : (5 : ℕ).Coprime (2 ^ e) := Nat.Coprime.pow_right _ (by norm_num)
    rw [hN] at h5
    exact this.dvd_of_dvd_mul_left h5
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card G) Nat.card_pos.ne'
  obtain ⟨k, hk, hk1, hk2, σ, hσ⟩ := cyclotomic_frobenius_exists Nat.prime_two hN hpM hM hζ
  obtain ⟨τ, hτ, -, hdeg, -, -, -, hblock, h2el⟩ := frobenius_galois_block_stability basis ideal
    Nat.prime_two hN hpM hM (dvd_refl _) hζ hk hk1 hσ
  refine ⟨k, τ, ?_, ?_, hτ, hdeg, hblock, h2el⟩
  · have := (Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega : e ≠ 0)) hk1)
    rw [Nat.ModEq] at this
    omega
  · have := Nat.ModEq.of_dvd h5M hk2
    rw [Nat.ModEq] at this
    omega

end CFSG.LyonsUnitaryFour
