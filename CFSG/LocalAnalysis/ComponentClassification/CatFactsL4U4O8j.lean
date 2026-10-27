module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8i
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8f
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUf

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Subgroup Matrix
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {K : Type} [Field K] [Finite K] {b c : K}

abbrev gT {k : Type} [Field k] (δ : k) (t : extension δ) :
    SpecialLinearGroup (Fin 2) (extension δ) :=
  OIL.uE δ (t - 1) * OIL.lE δ 1 * OIL.uE δ (-1)

theorem conj_gT {p : ℕ} [Fact p.Prime] [CharP K p] (hQ0 : ∃ v, Q8 K b c v ≠ 0)
    (ψ : MulAut (G0 K b c)) (g : similarityPairs (Q8 K b c))
    (hg : matrixProjectiveConjugationHom (Q8 K b c) g = MulAut.congr (psiC K b c) ψ)
    (c₀ : K) [Fact (¬ IsSquare c₀)] (δ : (extension c₀)ˣ)
    (y : SpecialLinearGroup (Fin 2) (extension (δ : extension c₀)) →*
      orthogonalDerived (Q8 K b c))
    (hfix : ∀ h, ψ ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h))) =
      (theta K b c hQ0).symm (QuotientGroup.mk' _ (y h)))
    (t : extension (δ : extension c₀)) :
    matrixDerivedConjugation (Q8 K b c) g
      ((derivedEquiv (Q8 K b c)).symm (y (gT (δ : extension c₀) t))) =
      (derivedEquiv (Q8 K b c)).symm (y (gT (δ : extension c₀) t)) := by
  have : CharP (extension c₀) p := charP_of_injective_algebraMap (algebraMap K _).injective p
  have hu : ∀ u : SpecialLinearGroup (Fin 2) (extension (δ : extension c₀)), u ^ p = 1 →
      matrixDerivedConjugation (Q8 K b c) g ((derivedEquiv (Q8 K b c)).symm (y u)) =
        (derivedEquiv (Q8 K b c)).symm (y u) := fun u hu =>
    conj_eq_of_pow hQ0 ψ g hg (y u) (by rw [← map_pow, hu, map_one]) (hfix u)
  dsimp only [gT]
  rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul,
    hu _ (OIL.uE_pow_char _ _), hu _ (OIL.lE_pow_char _ _), hu _ (OIL.uE_pow_char _ _)]

omit [Finite K] in
theorem trace_conj (g : similarityPairs (Q8 K b c)) (X : matrixDerived (Q8 K b c)) :
    (matrixDerivedConjugation (Q8 K b c) g X).val.val.trace = g.val.right X.val.val.trace := by
  rw [matrixDerivedConjugation_val, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle,
    Units.inv_mul, one_mul]
  change (X.val.val.map g.val.right).trace = _
  exact (AddMonoidHom.map_trace (g.val.right : K →+ K) X.val.val).symm

theorem right_eq_one {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hK : Nat.card K = p ^ e) (hQ0 : ∃ v, Q8 K b c v ≠ 0)
    (ψ : MulAut (G0 K b c)) (g : similarityPairs (Q8 K b c))
    (hg : matrixProjectiveConjugationHom (Q8 K b c) g = MulAut.congr (psiC K b c) ψ)
    (c₀ : K) [Fact (¬ IsSquare c₀)] (δ : (extension c₀)ˣ) (h2 : (2 : extension c₀) ≠ 0)
    (χ : (Fin (2 * 4) → K) ≃ₗ[K] (Fin 4 → extension c₀))
    (y : SpecialLinearGroup (Fin 2) (extension (δ : extension c₀)) →*
      orthogonalDerived (Q8 K b c))
    (hy : ∀ h v, (y h).val.val v =
      χ.symm ((OIU.Umat δ h2 h : Matrix (Fin 4) (Fin 4) (extension c₀)) *ᵥ χ v))
    (hfix : ∀ h, ψ ((theta K b c hQ0).symm (QuotientGroup.mk'
      ((scalarSigns (Q8 K b c)).subgroupOf (orthogonalDerived (Q8 K b c))) (y h))) =
      (theta K b c hQ0).symm (QuotientGroup.mk' _ (y h))) :
    g.val.right = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp he hK
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have h2K : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have htr : ∀ t : extension (δ : extension c₀),
      g.val.right (2 * (t.re ^ 2 - (δ : extension c₀) * t.im ^ 2).re) =
        2 * (t.re ^ 2 - (δ : extension c₀) * t.im ^ 2).re := fun t => by
    have h1 := congrArg (fun X : matrixDerived (Q8 K b c) => X.val.val.trace)
      (conj_gT hQ0 ψ g hg c₀ δ y hfix t)
    rw [trace_conj, trace_derived c₀ χ _ _ (hy _),
      OIL.trace_rowOHom_gT δ h2 (hermitianCoordinates (δ : extension c₀) h2) t] at h1
    exact h1
  have := finite_extension c₀
  have : Fintype (extension c₀) := Fintype.ofFinite _
  have hqE : Fintype.card (extension c₀) % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, card_extension, hK, ← pow_mul]
    exact Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
  refine RingEquiv.ext fun k => ?_
  obtain ⟨a, a', ha⟩ := OFL.exists_norm_eq hqE δ.ne_zero (algebraMap K (extension c₀) (k / 2))
  have h1 := htr ⟨a, a'⟩
  change g.val.right (2 * (a ^ 2 - (δ : extension c₀) * a' ^ 2).re) =
    2 * (a ^ 2 - (δ : extension c₀) * a' ^ 2).re at h1
  rw [ha, QuadraticAlgebra.algebraMap_re, mul_div_cancel₀ k h2K] at h1
  exact h1

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
