module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructureGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructureNonsquare
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticIsotropy

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure

open CatalogueBOrthogonalScalarSquare CatalogueBOrthogonalScalarSquareField
  CatalogueBOrthogonalScalarSquareForms

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem scalar_square_centralizer_structure (ℓ f : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2)
    (_hf : 1 ≤ f) (hcard : Nat.card K = ℓ ^ f) (hn : 2 ≤ Module.finrank K V)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (A : V ≃ₗ[K] V) (d μ : Kˣ)
    (hsquare : ∀ x : V, A (A x) = (d : K) • x)
    (hsim : ∀ x y : V, Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y)
    (hnonscalar : ∀ c : K, A.toLinearMap ≠ c • (1 : Module.End K V)) :
    letI := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank K V by omega)
    ((μ : K) / (d : K) = 1 ∨ (μ : K) / (d : K) = -1) ∧
      (∀ x y : V, Q.polarBilin (A x) y = ((μ : K) / (d : K)) * Q.polarBilin x (A y)) ∧
      (∀ b : Kˣ, (d : K) = (b : K) ^ 2 →
        IsCompl (positiveSquareKernel A b) (negativeSquareKernel A b) ∧
          positiveSquareKernel A b ≠ ⊥ ∧ negativeSquareKernel A b ≠ ⊥ ∧
          ((μ : K) / (d : K) = 1 →
            (∀ x ∈ positiveSquareKernel A b, ∀ y ∈ negativeSquareKernel A b,
              Q.polarBilin x y = 0) ∧
            (LinearMap.BilinForm.restrict Q.polarBilin (positiveSquareKernel A b)).Nondegenerate ∧
            (LinearMap.BilinForm.restrict Q.polarBilin (negativeSquareKernel A b)).Nondegenerate ∧
            ∃ e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
              (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (positiveSquareKernel A b).subtype) ×
                TauCeti.QuadraticMap.orthogonalGroup (Q.comp (negativeSquareKernel A b).subtype)),
              (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) (x : positiveSquareKernel A b),
                (((e g).1).val x).val = g.val.val x.val) ∧
              (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) (y : negativeSquareKernel A b),
                (((e g).2).val y).val = g.val.val y.val) ∧
              (∀ g (x : positiveSquareKernel A b) (y : negativeSquareKernel A b),
                (e.symm g).val.val (x.val + y.val) = (g.1.val x).val + (g.2.val y).val)) ∧
          ((μ : K) / (d : K) = -1 →
            (∀ x ∈ positiveSquareKernel A b, Q x = 0) ∧
            (∀ y ∈ negativeSquareKernel A b, Q y = 0) ∧
            (crossPairing Q.polarBilin (positiveSquareKernel A b)
              (negativeSquareKernel A b)).IsPerfPair ∧
            Module.finrank K (positiveSquareKernel A b) =
              Module.finrank K (negativeSquareKernel A b) ∧
            Module.finrank K (positiveSquareKernel A b) = Module.finrank K V / 2 ∧
            Module.finrank K (negativeSquareKernel A b) = Module.finrank K V / 2 ∧
            ∃ (e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
                (positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b))
              (dual : (positiveSquareKernel A b ≃ₗ[K] positiveSquareKernel A b) →
                (negativeSquareKernel A b ≃ₗ[K] negativeSquareKernel A b)),
              (∀ g (x : positiveSquareKernel A b) (y : negativeSquareKernel A b),
                Q.polarBilin x.val (dual g y).val = Q.polarBilin (g.symm x).val y.val) ∧
              (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) (x : positiveSquareKernel A b),
                (e g x).val = g.val.val x.val) ∧
              (∀ g (x : positiveSquareKernel A b), (e.symm g).val.val x.val = (g x).val) ∧
              (∀ g (y : negativeSquareKernel A b), (e.symm g).val.val y.val = (dual g y).val))) ∧
      (∀ hns : ¬ IsSquare (d : K),
        let hs := original_endomorphism_square A d hsquare
        letI := scalarField A.toLinearMap d hns hs
        letI := evaluationModule A.toLinearMap
        (IsField (scalarAlgebra A.toLinearMap) ∧ Finite (scalarAlgebra A.toLinearMap) ∧
          (generator A.toLinearMap).val = A.toLinearMap ∧
          generator A.toLinearMap ^ 2 = algebraMap K (scalarAlgebra A.toLinearMap) (d : K) ∧
          (∀ a : K, (algebraMap K (scalarAlgebra A.toLinearMap) a).val =
            algebraMap K (Module.End K V) a) ∧
          (∀ z : scalarAlgebra A.toLinearMap, ∃! p : K × K,
            coordinateElement A.toLinearMap p.1 p.2 = z) ∧
          (∀ F : Module.End K V, F ∈ scalarAlgebra A.toLinearMap ↔
            ∃ a b : K, F = algebraMap K (Module.End K V) a + b • A.toLinearMap) ∧
          Module.finrank K (scalarAlgebra A.toLinearMap) = 2 ∧
          Nat.card (scalarAlgebra A.toLinearMap) = (ℓ ^ f) ^ 2 ∧
          (∀ a b : K, a ≠ 0 ∨ b ≠ 0 →
            a ^ 2 - (d : K) * b ^ 2 ≠ 0 ∧
            (coordinateElement A.toLinearMap a b)⁻¹ = coordinateElement A.toLinearMap a (-b) /
              algebraMap K (scalarAlgebra A.toLinearMap) (a ^ 2 - (d : K) * b ^ 2)) ∧
          Function.Involutive (conjugation A.toLinearMap d hns hs) ∧
          conjugation A.toLinearMap d hns hs ≠ 1 ∧
          conjugation A.toLinearMap d hns hs (generator A.toLinearMap) = -generator A.toLinearMap ∧
          (∀ a b : K, conjugation A.toLinearMap d hns hs
            (coordinateElement A.toLinearMap a b) = coordinateElement A.toLinearMap a (-b)) ∧
          (∀ z : scalarAlgebra A.toLinearMap, conjugation A.toLinearMap d hns hs z = z ^ (ℓ ^ f)) ∧
          (∀ z : scalarAlgebra A.toLinearMap, conjugation A.toLinearMap d hns hs z = z ↔
            ∃ a : K, z = algebraMap K (scalarAlgebra A.toLinearMap) a) ∧
          (∀ (z : scalarAlgebra A.toLinearMap) (x : V), z • x = z.val x) ∧
          (∀ (a : K) (x : V), algebraMap K (scalarAlgebra A.toLinearMap) a • x = a • x) ∧
          IsScalarTower K (scalarAlgebra A.toLinearMap) V ∧
          Module.Finite (scalarAlgebra A.toLinearMap) V ∧
          Module.finrank K V = 2 * Module.finrank (scalarAlgebra A.toLinearMap) V ∧
          Module.finrank (scalarAlgebra A.toLinearMap) V = Module.finrank K V / 2) ∧
        (∀ hp : (μ : K) / (d : K) = 1,
          let hadj := positive_square_adjoint Q A d μ (Units.ne_zero d) hsquare hsim hp
          let BE := actualPositiveBilinear Q.polarBilin A.toLinearMap d (Units.ne_zero d) hns hs hadj
          let QE := actualPositiveQuadratic Q A.toLinearMap d (Units.ne_zero d) hns hs hadj
          BE.IsSymm ∧ BE.Nondegenerate ∧ QE.polarBilin = BE ∧ QE.polarBilin.Nondegenerate ∧
            (∀ x y, BE x y = algebraMap K (scalarAlgebra A.toLinearMap) (Q.polarBilin x y) +
              algebraMap K (scalarAlgebra A.toLinearMap) ((d : K)⁻¹ * Q.polarBilin (A x) y) *
                generator A.toLinearMap) ∧
            (∀ x, QE x = BE x x / 2) ∧
            ∃ e : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
              TauCeti.QuadraticMap.orthogonalGroup QE,
              (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) x, (e g).val x = g.val.val x) ∧
              (∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) x, (e.symm g).val.val x = g.val x) ∧
              (∀ (g : orthogonalOperatorCentralizer Q A.toLinearMap) x,
                (e g).val.symm x = g.val.val.symm x) ∧
              (∀ (g : TauCeti.QuadraticMap.orthogonalGroup QE) x,
                (e.symm g).val.val.symm x = g.val.symm x)) ∧
        (∀ hm : (μ : K) / (d : K) = -1,
          let hadj := negative_square_adjoint Q A d μ (Units.ne_zero d) hsquare hsim hm
          let h := actualNegativeHermitian Q.polarBilin A.toLinearMap d (Units.ne_zero d) hns hs hadj
          let bar := conjugation A.toLinearMap d hns hs
          h.IsSymm ∧ h.Nondegenerate ∧
            (∀ x y, h x y = algebraMap K (scalarAlgebra A.toLinearMap) (Q.polarBilin x y) +
              algebraMap K (scalarAlgebra A.toLinearMap) ((d : K)⁻¹ * Q.polarBilin x (A y)) *
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
                (e.symm g).val.val.symm x = g.val.symm x))) := by
  let := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank K V by omega)
  have h2 : (2 : K) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card
    (by rw [hcard]; exact (hℓ.odd_of_ne_two hodd).pow)
  refine ⟨original_similarity_ratio_sign Q hQ A d μ (Units.ne_zero d) hsquare hsim,
    scalar_square_adjoint Q.polarBilin A d μ (Units.ne_zero d) hsquare hsim,
    square_original_centralizer_structure Q hQ A d μ (Units.ne_zero d) h2 hsquare hsim hnonscalar,
    ?_⟩
  intro hns
  let hs := original_endomorphism_square A d hsquare
  let := scalarField A.toLinearMap d hns hs
  let := evaluationModule A.toLinearMap
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hcard] using original_nonsquare_field A d hns hsquare
  · intro hp
    exact original_positive_nonsquare_centralizer Q hQ A d μ (Units.ne_zero d) hns hsquare hsim hp
  · intro hm
    exact original_negative_nonsquare_centralizer Q hQ A d μ (Units.ne_zero d) hns hsquare hsim hm

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
