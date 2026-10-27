module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointReindexCovarianceBasic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CatalogueBOrthogonalSemilinear
open CatalogueBOrthogonalPointReindexCovariance

variable {H : Type} [Group H] {n p f : ℕ}

@[expose] def coordinatePlusWitnessEquiv (K : Type) [Field K]
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    H ≃* matrixProjectiveDerived (coordinateQuadPlus n K) :=
  e.trans (statedProjectiveReindexEquiv (plusIndexEquiv n)
    (quadPlus n K) (coe_quadPlus n K))

@[expose] def coordinateOddWitnessEquiv (K : Type) [Field K]
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    H ≃* matrixProjectiveDerived (coordinateQuadOdd n K) :=
  e.trans (statedProjectiveReindexEquiv (oddIndexEquiv n)
    (quadOdd n K) (coe_quadOdd n K))

@[expose] def coordinateMinusWitnessEquiv (K : Type) [Field K] (hn : 1 ≤ n) (b c : K)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    H ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn b c) :=
  e.trans (statedProjectiveReindexEquiv (minusIndexEquiv n hn)
    (quadMinus n K b c) (coe_quadMinus n K b c))

theorem coordinate_model_witness_plus
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    ringChar K = p ∧ (coordinateQuadPlus n K).polarBilin.Nondegenerate ∧
      (∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadPlus n K x = 0) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K),
        TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K)⁆ =
          elementaryGroup (coordinateQuadPlus n K) ∧
      CatalogueBOrthogonalPointAction.ActionProperties (coordinateQuadPlus n K)
        (projectivePointAction (coordinateQuadPlus n K)) ∧
      CatalogueBOrthogonalPointAction.ActionProperties (coordinateQuadPlus n K)
        ((projectivePointAction (coordinateQuadPlus n K)).comp
          (coordinatePlusWitnessEquiv K e).toMonoidHom) := by
  obtain ⟨hp, hf, hn⟩ := h.1
  have hr : 3 ≤ n := by omega
  have hreg := regular_coordinateQuadPlus n K hr
  have ha := coordinate_plus_point_action_properties n K hr
  exact ⟨ringChar_eq_of_card_eq hp hf hK, hreg.1, hreg.2,
    commutator_coordinateQuadPlus n K hr, ha,
    CatalogueBOrthogonalPointAction.actionProperties_equiv _ _ _
      (coordinatePlusWitnessEquiv K e) (fun _ => rfl) ha⟩

theorem coordinate_model_witness_odd
    (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    ringChar K = p ∧ (coordinateQuadOdd n K).polarBilin.Nondegenerate ∧
      (∃ T : Submodule K (Fin (2 * n + 1) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadOdd n K x = 0) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadOdd n K),
        TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadOdd n K)⁆ =
          elementaryGroup (coordinateQuadOdd n K) ∧
      CatalogueBOrthogonalPointAction.ActionProperties (coordinateQuadOdd n K)
        (projectivePointAction (coordinateQuadOdd n K)) ∧
      CatalogueBOrthogonalPointAction.ActionProperties (coordinateQuadOdd n K)
        ((projectivePointAction (coordinateQuadOdd n K)).comp
          (coordinateOddWitnessEquiv K e).toMonoidHom) := by
  obtain ⟨hp, hf, hn, hp2⟩ := h.1
  have hchar := ringChar_eq_of_card_eq hp hf hK
  have hprime : (ringChar K).Prime := hchar ▸ hp
  have h2 : (2 : K) ≠ 0 := by
    rw [Ne, two_eq_zero_iff_ringChar_eq_two hprime, hchar]
    exact hp2
  have hreg := regular_coordinateQuadOdd n K h2 hn
  have ha := coordinate_odd_point_action_properties n K h2 hn
  exact ⟨hchar, hreg.1, hreg.2, commutator_coordinateQuadOdd n K h2 hn, ha,
    CatalogueBOrthogonalPointAction.actionProperties_equiv _ _ _
      (coordinateOddWitnessEquiv K e) (fun _ => rfl) ha⟩

theorem coordinate_model_witness_minus
    (h : StatedClassicalModel H .POmegaMinus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    ringChar K = p ∧
      (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c).polarBilin.Nondegenerate ∧
      (∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧
        ∀ x ∈ T, coordinateQuadMinus n K (by have := h.1.2.2; omega) b c x = 0) ∧
      ⁅TauCeti.QuadraticMap.orthogonalGroup
          (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c),
        TauCeti.QuadraticMap.orthogonalGroup
          (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)⁆ =
          elementaryGroup (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c) ∧
      CatalogueBOrthogonalPointAction.ActionProperties
        (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)
        (projectivePointAction (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)) ∧
      CatalogueBOrthogonalPointAction.ActionProperties
        (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)
        ((projectivePointAction (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)).comp
          (coordinateMinusWitnessEquiv K (by have := h.1.2.2; omega) b c e).toMonoidHom) := by
  obtain ⟨hp, hf, hn⟩ := h.1
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  have ha := coordinate_minus_point_action_properties n K b c hn hirr
  exact ⟨ringChar_eq_of_card_eq hp hf hK, hreg.1, hreg.2,
    commutator_coordinateQuadMinus n K b c hn hirr, ha,
    CatalogueBOrthogonalPointAction.actionProperties_equiv _ _ _
      (coordinateMinusWitnessEquiv K (by omega) b c e) (fun _ => rfl) ha⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
