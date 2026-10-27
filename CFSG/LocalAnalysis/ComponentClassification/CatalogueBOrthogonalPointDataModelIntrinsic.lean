module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataIntrinsic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CatalogueBOrthogonalPointAction (Points ActionProperties actionStabilizer
  actionStabilizerFamily)

universe u v w

@[expose] def IntrinsicPointAction {K : Type u} [Field K] {V : Type v}
    [AddCommGroup V] [Module K V] {G : Type w} [Group G]
    (Q : QuadraticForm K V) (rho : G →* Equiv.Perm (Points Q)) : Prop :=
  Function.Injective rho ∧ Function.Injective (actionStabilizer Q rho) ∧
    ∀ L : Points Q,
      actionStabilizerFamily Q rho =
          Set.range (fun g : G =>
            (actionStabilizer Q rho L).map (MulAut.conj g).toMonoidHom) ∧
        IsCoatom (actionStabilizer Q rho L) ∧
        (actionStabilizer Q rho L).index = Nat.card (Points Q)

theorem intrinsicPointAction_of_properties {K : Type u} [Field K] {V : Type v}
    [AddCommGroup V] [Module K V] {G : Type w} [Group G]
    (Q : QuadraticForm K V) (rho : G →* Equiv.Perm (Points Q))
    (ha : ActionProperties Q rho) : IntrinsicPointAction Q rho :=
  ⟨pointAction_injective_of_properties Q rho ha,
    pointStabilizer_injective_of_properties Q rho ha, fun L =>
      ⟨pointFamily_eq_conjugacy_of_properties Q rho ha L,
        pointStabilizer_isCoatom_of_properties Q rho ha L,
        pointStabilizer_index_of_properties Q rho ha L⟩⟩

variable {H : Type} [Group H] {n p f : ℕ}

theorem coordinate_model_intrinsic_plus
    (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    coordinateQuadPlus n K ≠ 0 ∧
      IntrinsicPointAction (coordinateQuadPlus n K)
        (projectivePointAction (coordinateQuadPlus n K)) ∧
      IntrinsicPointAction (coordinateQuadPlus n K)
        ((projectivePointAction (coordinateQuadPlus n K)).comp
          (coordinatePlusWitnessEquiv K e).toMonoidHom) := by
  obtain ⟨_, hQ, hT, _, ha, hH⟩ := coordinate_model_witness_plus h K hK e
  exact ⟨quadratic_ne_zero_of_regular_three _ hQ hT,
    intrinsicPointAction_of_properties _ _ ha,
    intrinsicPointAction_of_properties _ _ hH⟩

theorem coordinate_model_intrinsic_odd
    (h : StatedClassicalModel H .POmegaOdd n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    coordinateQuadOdd n K ≠ 0 ∧
      IntrinsicPointAction (coordinateQuadOdd n K)
        (projectivePointAction (coordinateQuadOdd n K)) ∧
      IntrinsicPointAction (coordinateQuadOdd n K)
        ((projectivePointAction (coordinateQuadOdd n K)).comp
          (coordinateOddWitnessEquiv K e).toMonoidHom) := by
  obtain ⟨_, hQ, hT, _, ha, hH⟩ := coordinate_model_witness_odd h K hK e
  exact ⟨quadratic_ne_zero_of_regular_three _ hQ hT,
    intrinsicPointAction_of_properties _ _ ha,
    intrinsicPointAction_of_properties _ _ hH⟩

theorem coordinate_model_intrinsic_minus
    (h : StatedClassicalModel H .POmegaMinus n p f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    coordinateQuadMinus n K (by have := h.1.2.2; omega) b c ≠ 0 ∧
      IntrinsicPointAction (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)
        (projectivePointAction (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)) ∧
      IntrinsicPointAction (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)
        ((projectivePointAction (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c)).comp
          (coordinateMinusWitnessEquiv K (by have := h.1.2.2; omega) b c e).toMonoidHom) := by
  obtain ⟨_, hQ, hT, _, ha, hH⟩ := coordinate_model_witness_minus h K hK b c hirr e
  exact ⟨quadratic_ne_zero_of_regular_three _ hQ hT,
    intrinsicPointAction_of_properties _ _ ha,
    intrinsicPointAction_of_properties _ _ hH⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
