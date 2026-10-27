module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryRegular
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataGeometry

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CatalogueBOrthogonalPointIsometry

variable (n : ℕ) (K : Type) [Field K]

theorem regular_coordinateQuadPlus (hn : 3 ≤ n) :
    (coordinateQuadPlus n K).polarBilin.Nondegenerate ∧
      ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadPlus n K x = 0 := by
  have h := regular_quadPlus (K := K) hn
  exact ⟨polar_nondegenerate_isometry (coordinatePlusIsometry n K) h.1,
    singular_three_isometry (coordinatePlusIsometry n K) h.2⟩

theorem commutator_coordinateQuadPlus (hn : 3 ≤ n) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K),
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K)⁆ =
        elementaryGroup (coordinateQuadPlus n K) :=
  derived_eq_elementary_isometry (coordinatePlusIsometry n K)
    (commutator_orthogonalGroup_quadPlus hn)

theorem coordinate_plus_point_action_properties (hn : 3 ≤ n) :
    CatalogueBOrthogonalPointAction.ActionProperties (coordinateQuadPlus n K)
      (projectivePointAction (coordinateQuadPlus n K)) := by
  have h := regular_coordinateQuadPlus n K hn
  exact projective_point_action_properties (coordinateQuadPlus n K)
    (commutator_coordinateQuadPlus n K hn) h.1 h.2

theorem regular_coordinateQuadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    (coordinateQuadOdd n K).polarBilin.Nondegenerate ∧
      ∃ T : Submodule K (Fin (2 * n + 1) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadOdd n K x = 0 := by
  have h := regular_quadOdd h2 hn
  exact ⟨polar_nondegenerate_isometry (coordinateOddIsometry n K) h.1,
    singular_three_isometry (coordinateOddIsometry n K) h.2⟩

theorem commutator_coordinateQuadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadOdd n K),
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadOdd n K)⁆ =
        elementaryGroup (coordinateQuadOdd n K) :=
  derived_eq_elementary_isometry (coordinateOddIsometry n K)
    (commutator_orthogonalGroup_quadOdd h2 hn)

theorem coordinate_odd_point_action_properties (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    CatalogueBOrthogonalPointAction.ActionProperties (coordinateQuadOdd n K)
      (projectivePointAction (coordinateQuadOdd n K)) := by
  have h := regular_coordinateQuadOdd n K h2 hn
  exact projective_point_action_properties (coordinateQuadOdd n K)
    (commutator_coordinateQuadOdd n K h2 hn) h.1 h.2

variable [Finite K] (b c : K)

theorem regular_coordinateQuadMinus (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (coordinateQuadMinus n K (by omega) b c).polarBilin.Nondegenerate ∧
      ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadMinus n K (by omega) b c x = 0 := by
  have h := regular_quadMinus hn hirr
  exact ⟨polar_nondegenerate_isometry (coordinateMinusIsometry n K (by omega) b c) h.1,
    singular_three_isometry (coordinateMinusIsometry n K (by omega) b c) h.2⟩

theorem commutator_coordinateQuadMinus (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadMinus n K (by omega) b c),
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadMinus n K (by omega) b c)⁆ =
        elementaryGroup (coordinateQuadMinus n K (by omega) b c) :=
  derived_eq_elementary_isometry (coordinateMinusIsometry n K (by omega) b c)
    (commutator_orthogonalGroup_quadMinus hn hirr)

theorem coordinate_minus_point_action_properties (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CatalogueBOrthogonalPointAction.ActionProperties
      (coordinateQuadMinus n K (by omega) b c)
      (projectivePointAction (coordinateQuadMinus n K (by omega) b c)) := by
  have h := regular_coordinateQuadMinus n K b c hn hirr
  exact projective_point_action_properties (coordinateQuadMinus n K (by omega) b c)
    (commutator_coordinateQuadMinus n K b c hn hirr) h.1 h.2

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
