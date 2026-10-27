module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructureQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

theorem sixForm_original_norm (delta : K) (X : sixSubmodule delta) :
    sixForm delta X = (X.val 0 1).re * (X.val 2 3).re -
      QuadraticAlgebra.norm (X.val 0 2) + delta * (X.val 0 3).im * (X.val 1 2).im := by
  rw [sixForm_apply, extension_norm]
  ring

theorem six_original_entry_coordinates (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) :
    ∃ (a f : K) (b : extension delta) (r s : K),
      X.val 0 1 = algebraMap K (extension delta) a ∧
      X.val 2 3 = algebraMap K (extension delta) f ∧
      X.val 0 2 = b ∧ X.val 1 3 = conjugation delta b ∧
      X.val 0 3 = QuadraticAlgebra.omega * algebraMap K (extension delta) r ∧
      X.val 1 2 = QuadraticAlgebra.omega * algebraMap K (extension delta) s ∧
      sixForm delta X = a * f - QuadraticAlgebra.norm b + delta * r * s := by
  obtain ⟨ha, hf, hb, hc, hd⟩ := six_entries delta h2 X
  refine ⟨(X.val 0 1).re, (X.val 2 3).re, X.val 0 2,
    (X.val 0 3).im, (X.val 1 2).im,
    (conjugation_fixed_iff delta h2 _).mp ha,
    (conjugation_fixed_iff delta h2 _).mp hf, rfl, hb, ?_, ?_,
    sixForm_original_norm delta X⟩
  · rw [← six_generator_coordinate]
    apply QuadraticAlgebra.ext
    · exact (conjugation_anti_fixed_iff delta h2 _).mp hc
    · rfl
  · rw [← six_generator_coordinate]
    apply QuadraticAlgebra.ext
    · exact (conjugation_anti_fixed_iff delta h2 _).mp hd
    · rfl

theorem unitary_skew_six_full_isometry_structure (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) :
    (∀ X : sixSubmodule delta, ∃ (a f : K) (b : extension delta) (r s : K),
      X.val 0 1 = algebraMap K (extension delta) a ∧
      X.val 2 3 = algebraMap K (extension delta) f ∧
      X.val 0 2 = b ∧ X.val 1 3 = conjugation delta b ∧
      X.val 0 3 = QuadraticAlgebra.omega * algebraMap K (extension delta) r ∧
      X.val 1 2 = QuadraticAlgebra.omega * algebraMap K (extension delta) s ∧
      sixForm delta X = a * f - QuadraticAlgebra.norm b + delta * r * s) ∧
    (∀ X : sixSubmodule delta,
      algebraMap K (extension delta) (sixForm delta X) = pfaffian X.val) ∧
    Module.finrank K (sixSubmodule delta) = 6 ∧
    (sixForm delta).polarBilin.Nondegenerate ∧
    (∀ T : Submodule K (sixSubmodule delta),
      (∀ x ∈ T, sixForm delta x = 0) → Module.finrank K T ≤ 2) ∧
    (∀ (g : GL (Fin 4) (extension delta)) (a b : Kˣ),
      (sixBar delta g.val).transpose * sixGram (extension delta) * g.val =
        (a : K) • sixGram (extension delta) →
      (sixBar delta g.val).transpose * sixGram (extension delta) * g.val =
        (b : K) • sixGram (extension delta) → a = b) ∧
    (sixSpecialInclusion delta).range = (sixMultiplier delta).ker ∧
    (∀ (g : sixSimilitudes delta) (X : sixSubmodule delta),
      ((kappa delta h2 g).val X).val =
        (sixMultiplier delta g : K)⁻¹ • (g.val.val * X.val * g.val.val.transpose)) ∧
    (∀ g : sixSpecialUnitary delta, sixSpecialKappa delta h2 g = 1 ↔
      g.val.val = 1 ∨ g.val.val = -(1 : Matrix (Fin 4) (Fin 4) (extension delta))) ∧
    (sixSpecialKappa delta h2).ker ≤ Subgroup.center (sixSpecialUnitary delta) ∧
    (∀ X : sixSubmodule delta, ((sixGamma delta).val X).val = sixBar delta X.val) ∧
    sixGamma delta * sixGamma delta = 1 ∧
    (∀ g : sixSimilitudes delta,
      sixGamma delta * kappa delta h2 g * sixGamma delta =
        kappa delta h2 (sixConjugateD delta g)) ∧
    sixGenerated delta h2 = ⊤ ∧
    (sixSpecialImage delta h2).Normal ∧
    (∃ A : Subgroup (SixSpecialQuotient delta h2),
      A.Normal ∧ IsMulCommutative A ∧ A.index ≤ 2 ∧
        Group.IsSolvable (SixSpecialQuotient delta h2)) :=
  ⟨six_original_entry_coordinates delta h2, sixForm_pfaffian delta h2, six_finrank delta h2,
    sixForm_nondegenerate delta h2, six_totally_singular_finrank_le_two delta h2,
    six_multiplier_unique delta, sixSpecialInclusion_range delta,
    kappa_val delta h2, sixSpecialKappa_kernel_matrix_iff delta h2,
    sixSpecialKappa_kernel_central delta h2, sixGamma_val delta, sixGamma_square delta,
    sixGamma_kappa_gamma delta h2, sixGenerated_eq_top delta h2,
    inferInstance, six_full_isometry_quotient_structure delta h2⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
