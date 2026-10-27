module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldFrobenius

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

theorem scalar_square_actual_field_structure [Nontrivial V]
    (T : Module.End K V) (d : K) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    IsField (scalarAlgebra T) ∧
      (generator T).val = T ∧
      generator T ^ 2 = algebraMap K (scalarAlgebra T) d ∧
      (∀ a : K, (algebraMap K (scalarAlgebra T) a).val =
        algebraMap K (Module.End K V) a) ∧
      (∀ z : scalarAlgebra T, ∃! p : K × K, coordinateElement T p.1 p.2 = z) ∧
      (∀ F : Module.End K V, F ∈ scalarAlgebra T ↔
        ∃ a b : K, F = algebraMap K (Module.End K V) a + b • T) ∧
      Module.finrank K (scalarAlgebra T) = 2 ∧
      Nat.card (scalarAlgebra T) = Nat.card K ^ 2 ∧
      (∀ a b : K, a ≠ 0 ∨ b ≠ 0 →
        a ^ 2 - d * b ^ 2 ≠ 0 ∧
        (coordinateElement T a b)⁻¹ = coordinateElement T a (-b) /
          algebraMap K (scalarAlgebra T) (a ^ 2 - d * b ^ 2) ∧
        ((coordinateElement T a b)⁻¹).val = (a ^ 2 - d * b ^ 2)⁻¹ •
          (algebraMap K (Module.End K V) a - b • T)) ∧
      Function.Involutive (conjugation T d hns hsquare) ∧
      conjugation T d hns hsquare (generator T) = -generator T ∧
      (∀ a b : K, conjugation T d hns hsquare (coordinateElement T a b) =
        coordinateElement T a (-b)) ∧
      ((2 : K) ≠ 0 → conjugation T d hns hsquare ≠ 1 ∧
        ∀ z : scalarAlgebra T, conjugation T d hns hsquare z = z ↔
          ∃ a : K, z = algebraMap K (scalarAlgebra T) a) ∧
      (∀ z : scalarAlgebra T, ∀ v : V, z • v = z.val v) ∧
      (∀ a : K, ∀ v : V, algebraMap K (scalarAlgebra T) a • v = a • v) ∧
      IsScalarTower K (scalarAlgebra T) V ∧
      Module.finrank K V = 2 * Module.finrank (scalarAlgebra T) V ∧
      Module.finrank (scalarAlgebra T) V = Module.finrank K V / 2 ∧
      (∀ L : Module.End K V, Commute L T ↔
        ∀ (z : scalarAlgebra T) (v : V), L (z • v) = z • L v) ∧
      (∀ L : Module.End K V, Commute L T ↔
        ∃ F : Module.End (scalarAlgebra T) V, ∀ v : V, F v = L v) := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  refine ⟨?_, generator_val T, generator_square T d hsquare,
    scalarAlgebra_algebraMap_val T, existsUnique_coordinates T d hns hsquare,
    mem_scalarAlgebra_iff T d hns hsquare, scalarAlgebra_finrank T d hns hsquare,
    scalarAlgebra_card T d hns hsquare, ?_, conjugation_involutive T d hns hsquare,
    conjugation_generator T d hns hsquare, conjugation_coordinates T d hns hsquare,
    ?_, evaluation_smul T, evaluation_algebraMap_smul T, evaluationScalarTower T,
    evaluationModule_finrank T d hns hsquare, evaluationModule_finrank_div_two T d hns hsquare,
    commute_iff_evaluation_linear T, commute_iff_exists_evaluationLinearMap T⟩
  · exact Field.toIsField (scalarAlgebra T)
  · intro a b hab
    exact ⟨coordinate_denominator_ne_zero d hns a b hab,
      coordinateElement_inv T d hns hsquare a b hab,
      coordinateElement_inv_val T d hns hsquare a b hab⟩
  · intro h2
    exact ⟨conjugation_ne_one T d hns hsquare h2,
      conjugation_fixed_iff T d hns hsquare h2⟩

theorem scalar_square_actual_finite_dimension [Nontrivial V] [Module.Finite K V]
    (T : Module.End K V) (d : K) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    letI := scalarField T d hns hsquare
    letI := evaluationModule T
    Module.Finite (scalarAlgebra T) V ∧
      Module.finrank K V = 2 * Module.finrank (scalarAlgebra T) V ∧
      Module.finrank (scalarAlgebra T) V = Module.finrank K V / 2 := by
  let := scalarField T d hns hsquare
  let := evaluationModule T
  exact ⟨evaluationModule_finite T, evaluationModule_finrank T d hns hsquare,
    evaluationModule_finrank_div_two T d hns hsquare⟩

theorem scalar_square_finite_actual_field_structure [Finite K] [Nontrivial V]
    (T : Module.End K V) (d : K) (hns : ¬ IsSquare d)
    (hsquare : T ^ 2 = algebraMap K (Module.End K V) d) :
    letI := scalarField T d hns hsquare
    Nat.card (scalarAlgebra T) = Nat.card K ^ 2 ∧
      conjugation T d hns hsquare ≠ 1 ∧
      Function.Involutive (conjugation T d hns hsquare) ∧
      conjugation T d hns hsquare (generator T) = -generator T ∧
      (∀ z : scalarAlgebra T, conjugation T d hns hsquare z = z ^ Nat.card K) ∧
      (∀ z : scalarAlgebra T, conjugation T d hns hsquare z = z ↔
        ∃ a : K, z = algebraMap K (scalarAlgebra T) a) := by
  let := scalarField T d hns hsquare
  have h2 := finite_nonsquare_two_ne_zero d hns
  exact ⟨scalarAlgebra_card T d hns hsquare, conjugation_ne_one T d hns hsquare h2,
    conjugation_involutive T d hns hsquare, conjugation_generator T d hns hsquare,
    finite_conjugation_eq_card_power T d hns hsquare, conjugation_fixed_iff T d hns hsquare h2⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareField
