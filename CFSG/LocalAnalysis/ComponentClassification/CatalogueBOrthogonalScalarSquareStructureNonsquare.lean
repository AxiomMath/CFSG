module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareForms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareFieldFrobenius

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure

open CatalogueBOrthogonalScalarSquare CatalogueBOrthogonalScalarSquareField
  CatalogueBOrthogonalScalarSquareForms

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem original_endomorphism_square (A : V ≃ₗ[K] V) (d : K)
    (hsquare : ∀ x : V, A (A x) = d • x) :
    A.toLinearMap ^ 2 = algebraMap K (Module.End K V) d := by
  ext x
  exact hsquare x

variable [Finite K] [FiniteDimensional K V] [Nontrivial V]

theorem original_nonsquare_field (A : V ≃ₗ[K] V) (d : K)
    (hns : ¬ IsSquare d) (hsquare : ∀ x : V, A (A x) = d • x) :
    let hs := original_endomorphism_square A d hsquare
    letI := scalarField A.toLinearMap d hns hs
    letI := evaluationModule A.toLinearMap
    IsField (scalarAlgebra A.toLinearMap) ∧ Finite (scalarAlgebra A.toLinearMap) ∧
      (generator A.toLinearMap).val = A.toLinearMap ∧
      generator A.toLinearMap ^ 2 = algebraMap K (scalarAlgebra A.toLinearMap) d ∧
      (∀ a : K, (algebraMap K (scalarAlgebra A.toLinearMap) a).val =
        algebraMap K (Module.End K V) a) ∧
      (∀ z : scalarAlgebra A.toLinearMap, ∃! p : K × K,
        coordinateElement A.toLinearMap p.1 p.2 = z) ∧
      (∀ F : Module.End K V, F ∈ scalarAlgebra A.toLinearMap ↔
        ∃ a b : K, F = algebraMap K (Module.End K V) a + b • A.toLinearMap) ∧
      Module.finrank K (scalarAlgebra A.toLinearMap) = 2 ∧
      Nat.card (scalarAlgebra A.toLinearMap) = Nat.card K ^ 2 ∧
      (∀ a b : K, a ≠ 0 ∨ b ≠ 0 →
        a ^ 2 - d * b ^ 2 ≠ 0 ∧
        (coordinateElement A.toLinearMap a b)⁻¹ = coordinateElement A.toLinearMap a (-b) /
          algebraMap K (scalarAlgebra A.toLinearMap) (a ^ 2 - d * b ^ 2)) ∧
      Function.Involutive (conjugation A.toLinearMap d hns hs) ∧
      conjugation A.toLinearMap d hns hs ≠ 1 ∧
      conjugation A.toLinearMap d hns hs (generator A.toLinearMap) = -generator A.toLinearMap ∧
      (∀ a b : K, conjugation A.toLinearMap d hns hs
        (coordinateElement A.toLinearMap a b) = coordinateElement A.toLinearMap a (-b)) ∧
      (∀ z : scalarAlgebra A.toLinearMap, conjugation A.toLinearMap d hns hs z = z ^ Nat.card K) ∧
      (∀ z : scalarAlgebra A.toLinearMap, conjugation A.toLinearMap d hns hs z = z ↔
        ∃ a : K, z = algebraMap K (scalarAlgebra A.toLinearMap) a) ∧
      (∀ (z : scalarAlgebra A.toLinearMap) (x : V), z • x = z.val x) ∧
      (∀ (a : K) (x : V), algebraMap K (scalarAlgebra A.toLinearMap) a • x = a • x) ∧
      IsScalarTower K (scalarAlgebra A.toLinearMap) V ∧
      Module.Finite (scalarAlgebra A.toLinearMap) V ∧
      Module.finrank K V = 2 * Module.finrank (scalarAlgebra A.toLinearMap) V ∧
      Module.finrank (scalarAlgebra A.toLinearMap) V = Module.finrank K V / 2 := by
  let hs := original_endomorphism_square A d hsquare
  let := scalarField A.toLinearMap d hns hs
  let := evaluationModule A.toLinearMap
  refine ⟨Field.toIsField _, scalarAlgebra_finite_type _ d hns hs,
    generator_val _, generator_square _ d hs,
    scalarAlgebra_algebraMap_val _, existsUnique_coordinates _ d hns hs,
    mem_scalarAlgebra_iff _ d hns hs, scalarAlgebra_finrank _ d hns hs,
    scalarAlgebra_card _ d hns hs, ?_, conjugation_involutive _ d hns hs,
    conjugation_ne_one _ d hns hs (finite_nonsquare_two_ne_zero d hns),
    conjugation_generator _ d hns hs, conjugation_coordinates _ d hns hs,
    finite_conjugation_eq_card_power _ d hns hs,
    conjugation_fixed_iff _ d hns hs (finite_nonsquare_two_ne_zero d hns),
    evaluation_smul _, evaluation_algebraMap_smul _, evaluationScalarTower _,
    evaluationModule_finite _, evaluationModule_finrank _ d hns hs,
    evaluationModule_finrank_div_two _ d hns hs⟩
  intro a b hab
  exact ⟨coordinate_denominator_ne_zero d hns a b hab, coordinateElement_inv _ d hns hs a b hab⟩

omit [FiniteDimensional K V] in
theorem original_positive_nonsquare_centralizer (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ : K) (hd : d ≠ 0)
    (hns : ¬ IsSquare d) (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hp : μ / d = 1) :
    let hs := original_endomorphism_square A d hsquare
    letI := scalarField A.toLinearMap d hns hs
    letI := evaluationModule A.toLinearMap
    let hadj := positive_square_adjoint Q A d μ hd hsquare hsim hp
    let BE := actualPositiveBilinear Q.polarBilin A.toLinearMap d hd hns hs hadj
    let QE := actualPositiveQuadratic Q A.toLinearMap d hd hns hs hadj
    BE.IsSymm ∧ BE.Nondegenerate ∧ QE.polarBilin = BE ∧ QE.polarBilin.Nondegenerate ∧
      (∀ x y, BE x y = algebraMap K (scalarAlgebra A.toLinearMap) (Q.polarBilin x y) +
        algebraMap K (scalarAlgebra A.toLinearMap) (d⁻¹ * Q.polarBilin (A x) y) *
          generator A.toLinearMap) ∧
      (∀ x, QE x = BE x x / 2) ∧
      ∃ e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
        TauCeti.QuadraticMap.orthogonalGroup QE,
        (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) x, (e g).val x = g.val.val x) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) x, (e.symm g).val.val x = g.val x) ∧
        (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) x,
          (e g).val.symm x = g.val.val.symm x) ∧
        (∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) x,
          (e.symm g).val.val.symm x = g.val.symm x) :=
  positive_nonsquare_centralizer_structure Q hQ A.toLinearMap d hd hns
    (original_endomorphism_square A d hsquare) (finite_nonsquare_two_ne_zero d hns)
    (positive_square_adjoint Q A d μ hd hsquare hsim hp)

omit [FiniteDimensional K V] in
theorem original_negative_nonsquare_centralizer (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (A : V ≃ₗ[K] V) (d μ : K) (hd : d ≠ 0)
    (hns : ¬ IsSquare d) (hsquare : ∀ x : V, A (A x) = d • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = μ * Q.polarBilin x y)
    (hm : μ / d = -1) :
    let hs := original_endomorphism_square A d hsquare
    letI := scalarField A.toLinearMap d hns hs
    letI := evaluationModule A.toLinearMap
    let hadj := negative_square_adjoint Q A d μ hd hsquare hsim hm
    let h := actualNegativeHermitian Q.polarBilin A.toLinearMap d hd hns hs hadj
    let bar := conjugation A.toLinearMap d hns hs
    h.IsSymm ∧ h.Nondegenerate ∧
      (∀ x y, h x y = algebraMap K (scalarAlgebra A.toLinearMap) (Q.polarBilin x y) +
        algebraMap K (scalarAlgebra A.toLinearMap) (d⁻¹ * Q.polarBilin x (A y)) *
          generator A.toLinearMap) ∧
      (∀ (z : scalarAlgebra A.toLinearMap) x y, h (z • x) y = bar z * h x y) ∧
      (∀ (z : scalarAlgebra A.toLinearMap) x y, h x (z • y) = z * h x y) ∧
      (∀ x y, h y x = bar (h x y)) ∧
      ∃ e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
        CatalogueBUnitaryIsometry.isometryGroup h,
        (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) x, (e g).val x = g.val.val x) ∧
        (∀ (g : CatalogueBUnitaryIsometry.isometryGroup h) x, (e.symm g).val.val x = g.val x) ∧
        (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) x,
          (e g).val.symm x = g.val.val.symm x) ∧
        (∀ (g : CatalogueBUnitaryIsometry.isometryGroup h) x,
          (e.symm g).val.val.symm x = g.val.symm x) :=
  negative_nonsquare_centralizer_structure Q hQ A.toLinearMap d hd hns
    (original_endomorphism_square A d hsquare) (finite_nonsquare_two_ne_zero d hns)
    (negative_square_adjoint Q A d μ hd hsquare hsim hm)

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
