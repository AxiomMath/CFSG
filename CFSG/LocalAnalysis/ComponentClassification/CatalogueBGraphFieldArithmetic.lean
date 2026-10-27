module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldConjugacy

public section

namespace CFSG.ComponentClassification.CatalogueBGraphField

noncomputable section

open Matrix CatalogueBHigherLinearAction CatalogueBUnitaryTwo

universe u

theorem even_exponent_half_pos (f : ℕ) (hf : 1 ≤ f) (heven : Even f) :
    1 ≤ f / 2 := by
  have h := Nat.div_two_mul_two_of_even heven
  omega

theorem even_exponent_quadratic_card (K : Type u) (p f : ℕ)
    (hcard : Nat.card K = p ^ f) (heven : Even f) :
    Nat.card K = (p ^ (f / 2)) ^ 2 := by
  rw [← pow_mul, Nat.div_two_mul_two_of_even heven]
  exact hcard

theorem odd_fixed_field_parameter_ne (n : ℕ) (K : Type u) [Field K]
    (p e : ℕ) (hpodd : Odd p) (sigma : K ≃+* K)
    (hfixed : Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) = p ^ e) :
    (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2) := by
  intro h
  have htwo := congrArg Prod.snd h
  change Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) = 2 at htwo
  have ho : Odd (Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) := by
    rw [hfixed]
    exact hpodd.pow
  rw [htwo] at ho
  norm_num at ho

theorem odd_prime_power_three_le (p e : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (he : 1 ≤ e) : 3 ≤ p ^ e := by
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have hpower : p ≤ p ^ e := by
    simpa only [pow_one] using Nat.pow_le_pow_right hp.pos he
  omega

theorem unitaryFieldConjugation_eq_original (K : Type u) [Field K] [Finite K]
    (p e : ℕ) [Fact p.Prime] (hcard : Nat.card K = (p ^ e) ^ 2)
    (sigma : K ≃+* K) (hformula : ∀ x : K, sigma x = x ^ (p ^ e)) :
    unitaryFieldConjugation p e hcard = sigma := by
  ext x
  rw [unitaryFieldConjugation_apply]
  exact (hformula x).symm

theorem odd_graphField_unitary_data
    (n : ℕ) (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (A : GL (Fin n) K) (sigma : K ≃+* K) (hne : sigma ≠ 1)
    (hsquare : graphFieldAction n K A sigma ^ 2 = 1) :
    Even f ∧ 1 ≤ f / 2 ∧
      ∃ hunitary : Nat.card K = (p ^ (f / 2)) ^ 2,
        (letI : Fact p.Prime := ⟨hp⟩
         unitaryFieldConjugation p (f / 2) hunitary = sigma) ∧
        (∀ x : K, sigma x = x ^ (p ^ (f / 2))) ∧
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma) = p ^ (f / 2) ∧
        (n, Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K sigma)) ≠ (3, 2) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsigma, _⟩ := graphField_involution_conjugacy n K hn A sigma hne hsquare
  obtain ⟨heven, hformula, hfixed⟩ :=
    CatalogueBLinearTwoDescent.quadraticField_parameters K p f hp hcard sigma hsigma hne
  have hunitary := even_exponent_quadratic_card K p f hcard heven
  exact ⟨heven, even_exponent_half_pos f hf heven, hunitary,
    unitaryFieldConjugation_eq_original K p (f / 2) hunitary sigma hformula,
    hformula, hfixed, odd_fixed_field_parameter_ne n K p (f / 2) hpodd sigma hfixed⟩

end

end CFSG.ComponentClassification.CatalogueBGraphField
