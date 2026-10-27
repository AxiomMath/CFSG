module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionOrbits
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalPointCount
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointCount

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction

universe u v

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)

@[expose] def pointCountEquiv : Points Q ≃ singularLinesIn Q ⊤ where
  toFun L := ⟨L.val, le_top, L.property⟩
  invFun L := ⟨L.val, L.property.2⟩
  left_inv L := Subtype.ext (show L.val = L.val from rfl)
  right_inv L := Subtype.ext (show L.val = L.val from rfl)

theorem pointCountEquiv_submodule (L : Points Q) :
    (pointCountEquiv Q L).val = L.val := rfl

theorem pointCountEquiv_symm_submodule (L : singularLinesIn Q ⊤) :
    ((pointCountEquiv Q).symm L).val = L.val := rfl

variable {Q}

theorem pointPerp_hyperbolic_line (P : HypPair Q) (L M : Points Q)
    (hL : L.val = K ∙ P.e) :
    PointPerp L M ↔ ∀ x ∈ M.val, polar Q P.e x = 0 := by
  constructor
  · intro h x hx
    exact h P.e (hL ▸ Submodule.mem_span_singleton_self P.e) x hx
  · intro h x hx y hy
    rw [hL, Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [polar_smul_left_eq, h y hy, mul_zero]

@[expose] def perpendicularCountEquiv (P : HypPair Q) (L : Points Q)
    (hL : L.val = K ∙ P.e) :
    perpendicularPoints Q L ≃
      {M : Submodule K V | M ∈ singularLinesIn Q ⊤ ∧ M ≠ K ∙ P.e ∧
        ∀ x ∈ M, polar Q P.e x = 0} where
  toFun M := ⟨M.val.val, ⟨le_top, M.val.property⟩,
    (fun h => M.property.1 (Subtype.ext (h.trans hL.symm))),
    (pointPerp_hyperbolic_line P L M.val hL).mp M.property.2⟩
  invFun M := ⟨⟨M.val, M.property.1.2⟩,
    (fun h => M.property.2.1 ((congrArg Subtype.val h).trans hL)),
    (pointPerp_hyperbolic_line P L ⟨M.val, M.property.1.2⟩ hL).mpr M.property.2.2⟩
  left_inv M := Subtype.ext (Subtype.ext (show M.val.val = M.val.val from rfl))
  right_inv M := Subtype.ext (show M.val = M.val from rfl)

theorem perpendicularCountEquiv_submodule (P : HypPair Q) (L : Points Q)
    (hL : L.val = K ∙ P.e) (M : perpendicularPoints Q L) :
    (perpendicularCountEquiv P L hL M).val = M.val.val := rfl

@[expose] def nonperpendicularCountEquiv (P : HypPair Q) (L : Points Q)
    (hL : L.val = K ∙ P.e) :
    nonperpendicularPoints Q L ≃
      {M : Submodule K V | M ∈ singularLinesIn Q ⊤ ∧
        ∃ x ∈ M, polar Q P.e x ≠ 0} := by
  classical
  refine
    { toFun := fun M => ⟨M.val.val, ⟨le_top, M.val.property⟩, ?_⟩
      invFun := fun M => ⟨⟨M.val, M.property.1.2⟩, ?_⟩
      left_inv := fun M => Subtype.ext (Subtype.ext (show M.val.val = M.val.val from rfl))
      right_inv := fun M => Subtype.ext (show M.val = M.val from rfl) }
  · have h : ¬ PointPerp L M.val := M.property
    rw [pointPerp_hyperbolic_line P L M.val hL] at h
    push Not at h
    exact h
  · intro h
    obtain ⟨x, hx, hne⟩ := M.property.2
    exact hne ((pointPerp_hyperbolic_line P L ⟨M.val, M.property.1.2⟩ hL).mp h x hx)

theorem nonperpendicularCountEquiv_submodule (P : HypPair Q) (L : Points Q)
    (hL : L.val = K ∙ P.e) (M : nonperpendicularPoints Q L) :
    (nonperpendicularCountEquiv P L hL M).val = M.val.val := rfl

variable [FiniteDimensional K V]

theorem hyperbolic_perp_finrank (P : HypPair Q) :
    Module.finrank K P.perp = Module.finrank K V - 2 := by
  have h := finrank_inf_perp_add_two P (S := ⊤) Submodule.mem_top Submodule.mem_top
  have htop : (⊤ : Submodule K V) ⊓ P.perp = P.perp := inf_of_le_right le_top
  rw [htop, finrank_top] at h
  rw [← h, Nat.add_sub_cancel]

variable [Finite K]

theorem point_count_recurrence (P : HypPair Q) :
    Nat.card (Points Q) = 1 + Nat.card K * Nat.card (singularLinesIn Q P.perp) +
      Nat.card K ^ (Module.finrank K V - 2) := by
  rw [Nat.card_congr (pointCountEquiv Q),
    (orthogonal_geometry_hyperbolic_point_count P).1, hyperbolic_perp_finrank P]

theorem perpendicular_point_count (P : HypPair Q) (L : Points Q)
    (hL : L.val = K ∙ P.e) :
    Nat.card (perpendicularPoints Q L) =
      Nat.card K * Nat.card (singularLinesIn Q P.perp) := by
  rw [Nat.card_congr (perpendicularCountEquiv P L hL)]
  exact (orthogonal_geometry_hyperbolic_point_count P).2.1

theorem nonperpendicular_point_count (P : HypPair Q) (L : Points Q)
    (hL : L.val = K ∙ P.e) :
    Nat.card (nonperpendicularPoints Q L) = Nat.card K ^ (Module.finrank K V - 2) := by
  rw [Nat.card_congr (nonperpendicularCountEquiv P L hL)]
  rw [(orthogonal_geometry_hyperbolic_point_count P).2.2.1, hyperbolic_perp_finrank P]

theorem point_count_congruence (P : HypPair Q) (hP : 1 ≤ Module.finrank K P.perp) :
    Nat.card (Points Q) ≡ 1 [MOD Nat.card K] := by
  rw [Nat.card_congr (pointCountEquiv Q)]
  exact (orthogonal_geometry_hyperbolic_point_count P).2.2.2 hP

end CFSG.ComponentClassification.CatalogueBOrthogonalPointCount
