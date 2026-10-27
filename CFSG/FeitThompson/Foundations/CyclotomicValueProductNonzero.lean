module

public import CFSG.FeitThompson.Foundations.CyclotomicIrreducibleRat
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

private lemma pow_injOn_coprimeIndices {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    Set.InjOn (fun a : ℕ => ζ ^ a) (coprimeIndices n) := by
  have key : ∀ a b : ℕ, 1 ≤ a → a ≤ n → 1 ≤ b → b ≤ n → a ≤ b → ζ ^ a = ζ ^ b → a = b := by
    intro a b ha1 han hb1 hbn hab h
    have hne : ζ ^ a ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by omega))
    have h1 : ζ ^ a * ζ ^ (b - a) = ζ ^ a * 1 := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab]; exact h.symm
    have h3 : n ∣ b - a := hζ.dvd_of_pow_eq_one _ (mul_left_cancel₀ hne h1)
    have h4 : b - a = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega
  intro a ha b hb hab
  simp only [Finset.mem_coe, mem_coprimeIndices] at ha hb
  simp only at hab
  rcases le_total a b with h | h
  · exact key a b ha.1 ha.2.1 hb.1 hb.2.1 h hab
  · exact (key b a hb.1 hb.2.1 ha.1 ha.2.1 h hab.symm).symm

theorem prod_coprimeIndices_pow {M : Type*} [CommMonoid M] {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (f : ℂ → M) :
    ∏ a ∈ coprimeIndices n, f (ζ ^ a) = ∏ μ ∈ primitiveRoots n ℂ, f μ := by
  have : NeZero n := ⟨hn.ne'⟩
  refine Finset.prod_nbij (fun a => ζ ^ a) ?_ (pow_injOn_coprimeIndices hζ) ?_ (fun a _ => rfl)
  · intro a ha
    rw [mem_coprimeIndices] at ha
    exact (mem_primitiveRoots hn).2 (hζ.pow_of_coprime a ha.2.2)
  · intro μ hμ
    have hprim : IsPrimitiveRoot μ n := (mem_primitiveRoots hn).1 (by simpa using hμ)
    obtain ⟨i, hi, hiμ⟩ := hζ.eq_pow_of_pow_eq_one hprim.pow_eq_one
    have hcop : i.Coprime n := (hζ.pow_iff_coprime hn i).1 (hiμ ▸ hprim)
    by_cases h0 : i = 0
    · subst h0
      have hn1 : n = 1 := by simpa [Nat.Coprime] using hcop
      subst hn1
      refine ⟨1, by simp only [Finset.mem_coe, mem_coprimeIndices]; simp, ?_⟩
      simpa using hζ.pow_eq_one.trans hiμ
    · exact ⟨i, by
        simp only [Finset.mem_coe, mem_coprimeIndices]
        exact ⟨by omega, by omega, hcop⟩, hiμ⟩

theorem aeval_pow_ne_zero_of_aeval_ne_zero {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) {A : ℤ[X]} (hA : aeval ζ A ≠ 0) {a : ℕ} (ha : a.Coprime n) :
    aeval (ζ ^ a) A ≠ 0 := by
  have hAQ : aeval ζ (A.map (algebraMap ℤ ℚ)) ≠ 0 := by rwa [aeval_map_algebraMap]
  intro h
  refine hAQ ?_
  rw [aeval_eq_zero_iff_cyclotomic_rat_dvd hn hζ,
    ← aeval_eq_zero_iff_cyclotomic_rat_dvd hn (hζ.pow_of_coprime a ha), aeval_map_algebraMap]
  exact h

theorem cast_resultant_cyclotomic_eq_prod {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (A : ℤ[X]) :
    ((resultant (cyclotomic n ℤ) A (cyclotomic n ℤ).natDegree A.natDegree : ℤ) : ℂ)
      = ∏ a ∈ coprimeIndices n, aeval (ζ ^ a) A := by
  have hmap : (Int.castRingHom ℂ) (resultant (cyclotomic n ℤ) A
      (cyclotomic n ℤ).natDegree A.natDegree)
      = resultant (cyclotomic n ℂ) (A.map (Int.castRingHom ℂ))
          (cyclotomic n ℤ).natDegree A.natDegree := by
    rw [← resultant_map_map, map_cyclotomic_int]
  have hdeg : (cyclotomic n ℤ).natDegree = (cyclotomic n ℂ).natDegree := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic]
  have hdegA : (A.map (Int.castRingHom ℂ)).natDegree = A.natDegree :=
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int A
  rw [show ((resultant (cyclotomic n ℤ) A (cyclotomic n ℤ).natDegree A.natDegree : ℤ) : ℂ)
      = (Int.castRingHom ℂ) _ from rfl, hmap, hdeg,
    resultant_eq_prod_eval _ _ _ (le_of_eq hdegA) (IsAlgClosed.splits _),
    (cyclotomic.monic n ℂ).leadingCoeff, one_pow, one_mul,
    ← primitiveRootFactorProd_eq_cyclotomic, roots_primitiveRootFactorProd hn,
    ← Finset.prod_eq_multiset_prod, ← prod_coprimeIndices_pow hn hζ]
  simp [aeval_def, eval_map]

theorem prod_aeval_pow_ne_zero {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {A : ℤ[X]} (hA : aeval ζ A ≠ 0) : ∏ a ∈ coprimeIndices n, aeval (ζ ^ a) A ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _a ha =>
    aeval_pow_ne_zero_of_aeval_ne_zero hn hζ hA (mem_coprimeIndices.1 ha).2.2

theorem resultant_cyclotomic_ne_zero {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {A : ℤ[X]} (hA : aeval ζ A ≠ 0) :
    resultant (cyclotomic n ℤ) A (cyclotomic n ℤ).natDegree A.natDegree ≠ 0 := by
  intro h
  refine prod_aeval_pow_ne_zero hn hζ hA ?_
  rw [← cast_resultant_cyclotomic_eq_prod hn hζ A, h, Int.cast_zero]

theorem exists_int_prod_aeval_pow_ne_zero {n : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) {A : ℤ[X]} (hA : aeval ζ A ≠ 0) :
    (∀ a ∈ coprimeIndices n, aeval (ζ ^ a) A ≠ 0) ∧
      ∃ m : ℤ, m ≠ 0 ∧ ∏ a ∈ coprimeIndices n, aeval (ζ ^ a) A = (m : ℂ) :=
  ⟨fun _a ha => aeval_pow_ne_zero_of_aeval_ne_zero hn hζ hA (mem_coprimeIndices.1 ha).2.2,
    resultant (cyclotomic n ℤ) A (cyclotomic n ℤ).natDegree A.natDegree,
    resultant_cyclotomic_ne_zero hn hζ hA, (cast_resultant_cyclotomic_eq_prod hn hζ A).symm⟩

end CFSG.FeitThompson
