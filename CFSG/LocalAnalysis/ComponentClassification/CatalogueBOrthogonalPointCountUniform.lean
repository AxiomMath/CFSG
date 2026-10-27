module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointCountNested

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointCount

open CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

@[expose] noncomputable def perpendicularElementaryEquiv (g : elementaryGroup Q)
    (L : Points Q) : perpendicularPoints Q L ≃ perpendicularPoints Q (g • L) :=
  (MulAction.toPerm g).subtypeEquiv (by
    intro M
    change (M ≠ L ∧ PointPerp L M) ↔ (g • M ≠ g • L ∧ PointPerp (g • L) (g • M))
    have hne : (g • M ≠ g • L) ↔ M ≠ L :=
      not_congr (MulAction.toPerm g).injective.eq_iff
    exact (and_congr hne (pointPerp_smul_iff g L M)).symm)

theorem perpendicularElementaryEquiv_apply (g : elementaryGroup Q) (L : Points Q)
    (M : perpendicularPoints Q L) :
    (perpendicularElementaryEquiv g L M).val = g • M.val := rfl

theorem perpendicularElementaryEquiv_symm_apply (g : elementaryGroup Q) (L : Points Q)
    (M : perpendicularPoints Q (g • L)) :
    ((perpendicularElementaryEquiv g L).symm M).val = g⁻¹ • M.val := rfl

@[expose] noncomputable def nonperpendicularElementaryEquiv (g : elementaryGroup Q)
    (L : Points Q) : nonperpendicularPoints Q L ≃ nonperpendicularPoints Q (g • L) :=
  (MulAction.toPerm g).subtypeEquiv (by
    intro M
    change ¬ PointPerp L M ↔ ¬ PointPerp (g • L) (g • M)
    exact (not_congr (pointPerp_smul_iff g L M)).symm)

theorem nonperpendicularElementaryEquiv_apply (g : elementaryGroup Q) (L : Points Q)
    (M : nonperpendicularPoints Q L) :
    (nonperpendicularElementaryEquiv g L M).val = g • M.val := rfl

theorem nonperpendicularElementaryEquiv_symm_apply (g : elementaryGroup Q) (L : Points Q)
    (M : nonperpendicularPoints Q (g • L)) :
    ((nonperpendicularElementaryEquiv g L).symm M).val = g⁻¹ • M.val := rfl

theorem perpendicular_point_count_smul (g : elementaryGroup Q) (L : Points Q) :
    Nat.card (perpendicularPoints Q (g • L)) = Nat.card (perpendicularPoints Q L) :=
  (Nat.card_congr (perpendicularElementaryEquiv g L)).symm

theorem nonperpendicular_point_count_smul (g : elementaryGroup Q) (L : Points Q) :
    Nat.card (nonperpendicularPoints Q (g • L)) = Nat.card (nonperpendicularPoints Q L) :=
  (Nat.card_congr (nonperpendicularElementaryEquiv g L)).symm

variable [FiniteDimensional K V]

theorem point_subdegree_uniformity (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (L M : Points Q) :
    Nat.card (perpendicularPoints Q L) = Nat.card (perpendicularPoints Q M) ∧
      Nat.card (nonperpendicularPoints Q L) = Nat.card (nonperpendicularPoints Q M) := by
  have h := elementary_projective_action Q hQ hT
  let : MulAction.IsPreprimitive (elementaryGroup Q) (Points Q) := h.2.2.2.2.2.1
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (elementaryGroup Q) L M
  exact ⟨(perpendicular_point_count_smul g L).symm,
    (nonperpendicular_point_count_smul g L).symm⟩

variable [Finite K]

theorem points_finite : Finite (Points Q) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (Submodule K V) :=
    Finite.of_injective (fun L : Submodule K V => (L : Set V)) SetLike.coe_injective
  change Finite {L : Submodule K V // Module.finrank K L = 1 ∧ ∀ x ∈ L, Q x = 0}
  infer_instance

theorem exists_uniform_unequal_subdegrees (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ a b : ℕ, a ≠ b ∧ ∀ L : Points Q,
      Nat.card (perpendicularPoints Q L) = a ∧ Nat.card (nonperpendicularPoints Q L) = b := by
  obtain ⟨L⟩ := (elementary_projective_action Q hQ hT).1
  refine ⟨Nat.card (perpendicularPoints Q L), Nat.card (nonperpendicularPoints Q L),
    (point_subdegree_divisibility hQ hT L).2.2.2, ?_⟩
  intro M
  exact point_subdegree_uniformity hQ hT M L

theorem exists_uniform_subdegrees_divisibility (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ a b : ℕ, a ≠ b ∧ Nat.card K ∣ a ∧ ¬ Nat.card K ^ 2 ∣ a ∧
      Nat.card K ^ 2 ∣ b ∧ ∀ L : Points Q,
        Nat.card (perpendicularPoints Q L) = a ∧ Nat.card (nonperpendicularPoints Q L) = b := by
  obtain ⟨L⟩ := (elementary_projective_action Q hQ hT).1
  have h := point_subdegree_divisibility hQ hT L
  exact ⟨Nat.card (perpendicularPoints Q L), Nat.card (nonperpendicularPoints Q L),
    h.2.2.2, h.1, h.2.1, h.2.2.1, fun M => point_subdegree_uniformity hQ hT M L⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointCount
