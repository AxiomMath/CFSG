module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

def coprimeIndices (n : ℕ) : Finset ℕ := {a ∈ Finset.Icc 1 n | Nat.Coprime a n}

lemma mem_coprimeIndices {n a : ℕ} :
    a ∈ coprimeIndices n ↔ 1 ≤ a ∧ a ≤ n ∧ Nat.Coprime a n := by
  simp [coprimeIndices, and_assoc]

lemma card_coprimeIndices (n : ℕ) : (coprimeIndices n).card = Nat.totient n := by
  rw [← Nat.filter_coprime_Ico_eq_totient n 1]
  congr 1
  ext a
  simp only [coprimeIndices, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  rw [Nat.coprime_comm]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

noncomputable def primitiveRootFactorProd (n : ℕ) : ℂ[X] :=
  ∏ a ∈ coprimeIndices n,
    (X - C (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / (n : ℂ)))))

private lemma exp_two_pi_I_div_pow (n a : ℕ) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) ^ a
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / (n : ℂ))) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem primitiveRootFactorProd_eq_cyclotomic (n : ℕ) :
    primitiveRootFactorProd n = cyclotomic n ℂ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primitiveRootFactorProd, coprimeIndices]
  set ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ, primitiveRootFactorProd]
  refine Finset.prod_nbij
    (fun a => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / (n : ℂ)))) ?_ ?_ ?_ ?_
  · intro a ha
    rw [mem_coprimeIndices] at ha
    exact (mem_primitiveRoots hn).2
      (Complex.isPrimitiveRoot_exp_of_coprime a n hn.ne' ha.2.2)
  ·
    have key : ∀ a b : ℕ, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → a ≤ b → ζ ^ a = ζ ^ b → a = b := by
      intro a b ha1 han hb1 hbn hab h
      have hne : ζ ^ a ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
      have h1 : ζ ^ a * ζ ^ (b - a) = ζ ^ a * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab]
        exact h.symm
      have h3 : n ∣ b - a := hζ.dvd_of_pow_eq_one _ (mul_left_cancel₀ hne h1)
      have h4 : b - a = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
      omega
    intro a ha b hb hab
    simp only [Finset.mem_coe, mem_coprimeIndices] at ha hb
    have hab' : ζ ^ a = ζ ^ b := by
      rw [exp_two_pi_I_div_pow, exp_two_pi_I_div_pow]; exact hab
    rcases le_total a b with h | h
    · exact key a b ha.1 ha.2.1 hb.1 hb.2.1 h hab'
    · exact (key b a hb.1 hb.2.1 ha.1 ha.2.1 h hab'.symm).symm
  ·
    intro μ hμ
    have hprim : IsPrimitiveRoot μ n := (mem_primitiveRoots hn).1 (by simpa using hμ)
    obtain ⟨i, hi, hcop, hiμ⟩ := (Complex.isPrimitiveRoot_iff μ n hn.ne').1 hprim
    by_cases h0 : i = 0
    · subst h0
      have hn1 : n = 1 := by simpa [Nat.Coprime] using hcop
      subst hn1
      refine ⟨1, by simp only [Finset.mem_coe, mem_coprimeIndices]; simp, ?_⟩
      rw [← hiμ]
      norm_num [Complex.exp_two_pi_mul_I]
    · exact ⟨i, by
        simp only [Finset.mem_coe, mem_coprimeIndices]
        exact ⟨by omega, by omega, hcop⟩, hiμ⟩
  · intro a _
    rfl

theorem map_int_cyclotomic_eq (n : ℕ) :
    (cyclotomic n ℤ).map (Int.castRingHom ℂ) = primitiveRootFactorProd n := by
  rw [map_cyclotomic_int, primitiveRootFactorProd_eq_cyclotomic]

theorem exists_int_monic_map_eq_primitiveRootFactorProd (n : ℕ) :
    ∃ P : ℤ[X], P.Monic ∧ P.map (Int.castRingHom ℂ) = primitiveRootFactorProd n :=
  ⟨cyclotomic n ℤ, cyclotomic.monic n ℤ, map_int_cyclotomic_eq n⟩

theorem exists_int_coeff_primitiveRootFactorProd (n k : ℕ) :
    ∃ a : ℤ, (primitiveRootFactorProd n).coeff k = (a : ℂ) :=
  ⟨(cyclotomic n ℤ).coeff k, by rw [← map_int_cyclotomic_eq n, coeff_map]; rfl⟩

theorem monic_primitiveRootFactorProd (n : ℕ) : (primitiveRootFactorProd n).Monic := by
  rw [primitiveRootFactorProd_eq_cyclotomic]
  exact cyclotomic.monic n ℂ

theorem degree_primitiveRootFactorProd (n : ℕ) :
    (primitiveRootFactorProd n).degree = Nat.totient n := by
  rw [primitiveRootFactorProd_eq_cyclotomic, degree_cyclotomic]

theorem natDegree_primitiveRootFactorProd (n : ℕ) :
    (primitiveRootFactorProd n).natDegree = Nat.totient n := by
  rw [primitiveRootFactorProd_eq_cyclotomic, natDegree_cyclotomic]

theorem prod_primitiveRootFactorProd_divisors {n : ℕ} (hn : 0 < n) :
    ∏ d ∈ n.divisors, primitiveRootFactorProd d = X ^ n - 1 := by
  simp only [primitiveRootFactorProd_eq_cyclotomic]
  exact prod_cyclotomic_eq_X_pow_sub_one hn ℂ

theorem isRoot_primitiveRootFactorProd_iff {n : ℕ} (hn : 0 < n) {μ : ℂ} :
    (primitiveRootFactorProd n).IsRoot μ ↔ IsPrimitiveRoot μ n := by
  rw [primitiveRootFactorProd_eq_cyclotomic]
  exact isRoot_cyclotomic_iff_charZero hn

theorem roots_primitiveRootFactorProd {n : ℕ} (hn : 0 < n) :
    (primitiveRootFactorProd n).roots = (primitiveRoots n ℂ).val := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) n :=
    Complex.isPrimitiveRoot_exp n hn.ne'
  rw [primitiveRootFactorProd_eq_cyclotomic, cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
    roots_prod_X_sub_C]

theorem separable_primitiveRootFactorProd {n : ℕ} (hn : 0 < n) :
    (primitiveRootFactorProd n).Separable := by
  have : NeZero ((n : ℕ) : ℂ) := ⟨by simpa using hn.ne'⟩
  rw [primitiveRootFactorProd_eq_cyclotomic]
  exact separable_cyclotomic n ℂ

theorem roots_primitiveRootFactorProd_nodup {n : ℕ} (hn : 0 < n) :
    (primitiveRootFactorProd n).roots.Nodup :=
  nodup_roots (separable_primitiveRootFactorProd hn)

end CFSG.FeitThompson
