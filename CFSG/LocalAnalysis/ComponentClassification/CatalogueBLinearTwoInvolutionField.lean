module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoInvolution

noncomputable section

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo

universe u

theorem ringChar_ne_two_of_card (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card K = p ^ f) :
    ringChar K ≠ 2 := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow (show Fintype.card K = p ^ f by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  rw [ringChar.eq K p]
  intro h
  subst p
  exact (Nat.not_even_iff_odd.mpr hodd) even_two

theorem two_ne_zero_of_card (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hodd : Odd p) (hcard : Nat.card K = p ^ f) :
    (2 : K) ≠ 0 := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow (show Fintype.card K = p ^ f by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  intro htwo
  have hp2 : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp htwo
  rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with hp1 | hp2
  · exact hp.ne_one hp1
  · subst p
    exact (Nat.not_even_iff_odd.mpr hodd) even_two

theorem fixedField_mem_frobenius (K : Type u) [Field K]
    (p f : ℕ) (sigma : K ≃+* K)
    (hformula : ∀ x : K, sigma x = x ^ (p ^ (f / 2))) (x : K) :
    x ∈ CatalogueBLinearTwoFixed.fixedField K sigma ↔ x ^ (p ^ (f / 2)) = x := by
  rw [CatalogueBLinearTwoFixed.mem_fixedField_iff, hformula]

@[expose] def frobeniusFixedField (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hcard : Nat.card K = p ^ f) : Subfield K := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow (show Fintype.card K = p ^ f by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact (iterateFrobenius K p (f / 2)).eqLocusField (RingHom.id K)

theorem mem_frobeniusFixedField (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hcard : Nat.card K = p ^ f) (x : K) :
    x ∈ frobeniusFixedField K p f hp hcard ↔ x ^ (p ^ (f / 2)) = x := by
  let : Fintype K := Fintype.ofFinite K
  let : Fact p.Prime := ⟨hp⟩
  let : CharP K p := charP_of_card_eq_prime_pow (show Fintype.card K = p ^ f by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  change x ∈ (iterateFrobenius K p (f / 2)).eqLocusField (RingHom.id K) ↔ _
  rw [RingHom.mem_eqLocusField, iterateFrobenius_def]
  rfl

theorem fixedField_eq_frobeniusFixedField (K : Type u) [Field K] [Finite K]
    (p f : ℕ) (hp : p.Prime) (hcard : Nat.card K = p ^ f)
    (sigma : K ≃+* K) (hformula : ∀ x : K, sigma x = x ^ (p ^ (f / 2))) :
    CatalogueBLinearTwoFixed.fixedField K sigma = frobeniusFixedField K p f hp hcard := by
  ext x
  rw [fixedField_mem_frobenius K p f sigma hformula, mem_frobeniusFixedField]

theorem fixedField_card_odd (K : Type u) [Field K] [Finite K]
    (hodd : ringChar K ≠ 2) (sigma : K ≃+* K) :
    Odd (Nat.card (CatalogueBLinearTwoFixed.fixedField K sigma)) := by
  let F := CatalogueBLinearTwoFixed.fixedField K sigma
  let : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    rw [Algebra.ringChar_eq F K]
    exact hodd
  apply Nat.odd_iff.mpr
  simpa only [Nat.card_eq_fintype_card] using FiniteField.odd_card_of_char_ne_two hchar

theorem quadratic_card_three_iff (p f : ℕ) (hf : 1 ≤ f) (heven : Even f) :
    p ^ (f / 2) = 3 ↔ p = 3 ∧ f = 2 := by
  constructor
  · intro h
    obtain ⟨hp, hhalf⟩ := Nat.prime_three.pow_eq_iff.mp h
    obtain ⟨n, hn⟩ := heven
    exact ⟨hp, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem quadratic_card_ge_five (p f : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hf : 1 ≤ f) (heven : Even f) (hexception : ¬ (p = 3 ∧ f = 2)) :
    5 ≤ p ^ (f / 2) := by
  have hpge : 3 ≤ p := by
    have hp2 := hp.two_le
    obtain ⟨n, hn⟩ := hodd
    omega
  have hhalf : 1 ≤ f / 2 := by
    obtain ⟨n, hn⟩ := heven
    omega
  have hbound : 3 ≤ p ^ (f / 2) := hpge.trans (by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < p) hhalf)
  have hne3 : p ^ (f / 2) ≠ 3 := by
    intro h
    exact hexception ((quadratic_card_three_iff p f hf heven).mp h)
  have hpowodd : Odd (p ^ (f / 2)) := hodd.pow
  obtain ⟨n, hn⟩ := hpowodd
  omega

end

end CFSG.ComponentClassification.CatalogueBLinearTwoInvolution
