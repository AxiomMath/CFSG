module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointCountUniform
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointNormalizerRelation

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointModelNormalizer

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial
open CatalogueBOrthogonalPointAction

universe u v w w'

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)
variable {G : Type w} [Group G] {D : Type w'} [Group D]

@[expose] def PointCountGeometry : Prop :=
  Finite (Points Q) ∧
    (∀ (L : Points Q) (P : HypPair Q), L.val = K ∙ P.e →
      PolarNondegOn Q P.perp ∧ (Q.restrict P.perp).polarBilin.Nondegenerate ∧
      Module.finrank K P.perp = Module.finrank K V - 2 ∧
      Nat.card (perpendicularPoints Q L) =
        Nat.card K * Nat.card (singularLinesIn Q P.perp) ∧
      Nat.card (nonperpendicularPoints Q L) = Nat.card K ^ (Module.finrank K V - 2) ∧
      Nat.card (Points Q) = 1 + Nat.card K * Nat.card (singularLinesIn Q P.perp) +
        Nat.card K ^ (Module.finrank K V - 2)) ∧
    (∀ L : Points Q, Nat.card K ∣ Nat.card (perpendicularPoints Q L) ∧
      ¬ Nat.card K ^ 2 ∣ Nat.card (perpendicularPoints Q L) ∧
      Nat.card K ^ 2 ∣ Nat.card (nonperpendicularPoints Q L) ∧
      Nat.card (perpendicularPoints Q L) ≠ Nat.card (nonperpendicularPoints Q L)) ∧
    ∃ a b : ℕ, a ≠ b ∧ Nat.card K ∣ a ∧ ¬ Nat.card K ^ 2 ∣ a ∧
      Nat.card K ^ 2 ∣ b ∧ ∀ L : Points Q,
        Nat.card (perpendicularPoints Q L) = a ∧ Nat.card (nonperpendicularPoints Q L) = b

@[expose] def ActionNormalizerOrthogonality (ρ : G →* Equiv.Perm (Points Q)) : Prop :=
  ∀ φ : Equiv.Perm (Points Q), φ ∈ Subgroup.normalizer ρ.range →
    (∀ L M : Points Q, PointPerp (φ L) (φ M) ↔ PointPerp L M) ∧
    (∀ L : Points Q, φ '' perpendicularPoints Q L = perpendicularPoints Q (φ L)) ∧
    ∀ L : Points Q, φ '' nonperpendicularPoints Q L = nonperpendicularPoints Q (φ L)

theorem action_range_of_equiv (ρ : G →* Equiv.Perm (Points Q))
    (τ : D →* Equiv.Perm (Points Q)) (e : G ≃* D)
    (h : ∀ g : G, ρ g = τ (e g)) : ρ.range = τ.range := by
  ext φ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨e g, (h g).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    exact ⟨x, h x⟩

theorem action_range_comp_equiv (ρ : D →* Equiv.Perm (Points Q)) (e : G ≃* D) :
    (ρ.comp e.toMonoidHom).range = ρ.range :=
  action_range_of_equiv Q _ _ e (fun _ => rfl)

theorem action_normalizer_comp_equiv (ρ : D →* Equiv.Perm (Points Q)) (e : G ≃* D) :
    Subgroup.normalizer ((ρ.comp e.toMonoidHom).range : Set (Equiv.Perm (Points Q))) =
      Subgroup.normalizer (ρ.range : Set (Equiv.Perm (Points Q))) := by
  rw [action_range_comp_equiv Q ρ e]

section FiniteGeometry

variable [Finite K] [FiniteDimensional K V]

theorem regular_hyperbolic_point_counts (hQ : Q.polarBilin.Nondegenerate)
    (L : Points Q) (P : HypPair Q) (hL : L.val = K ∙ P.e) :
    PolarNondegOn Q P.perp ∧ (Q.restrict P.perp).polarBilin.Nondegenerate ∧
      Module.finrank K P.perp = Module.finrank K V - 2 ∧
      Nat.card (perpendicularPoints Q L) =
        Nat.card K * Nat.card (singularLinesIn Q P.perp) ∧
      Nat.card (nonperpendicularPoints Q L) = Nat.card K ^ (Module.finrank K V - 2) ∧
      Nat.card (Points Q) = 1 + Nat.card K * Nat.card (singularLinesIn Q P.perp) +
        Nat.card K ^ (Module.finrank K V - 2) := by
  have hP := HypPair.polarNondegOn_perp hQ P
  exact ⟨hP, nondegenerate_polarBilin_restrict hP,
    CatalogueBOrthogonalPointCount.hyperbolic_perp_finrank P,
    CatalogueBOrthogonalPointCount.perpendicular_point_count P L hL,
    CatalogueBOrthogonalPointCount.nonperpendicular_point_count P L hL,
    CatalogueBOrthogonalPointCount.point_count_recurrence P⟩

theorem point_count_geometry (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    PointCountGeometry Q :=
  ⟨CatalogueBOrthogonalPointCount.points_finite,
    regular_hyperbolic_point_counts Q hQ,
    CatalogueBOrthogonalPointCount.point_subdegree_divisibility hQ hT,
    CatalogueBOrthogonalPointCount.exists_uniform_subdegrees_divisibility hQ hT⟩

theorem action_normalizer_orthogonality (ρ : G →* Equiv.Perm (Points Q))
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hρ : ActionProperties Q ρ) : ActionNormalizerOrthogonality Q ρ := by
  let : Finite (Points Q) := CatalogueBOrthogonalPointCount.points_finite
  obtain ⟨a, b, hab, hcounts⟩ :=
    CatalogueBOrthogonalPointCount.exists_uniform_unequal_subdegrees hQ hT
  intro φ hφ
  exact ⟨CatalogueBOrthogonalPointNormalizer.pointPerp_normalizer_iff
      Q ρ φ hφ hρ a b (fun L => (hcounts L).1) (fun L => (hcounts L).2) hab,
    CatalogueBOrthogonalPointNormalizer.perpendicularPoints_normalizer_image
      Q ρ φ hφ hρ a b (fun L => (hcounts L).1) (fun L => (hcounts L).2) hab,
    CatalogueBOrthogonalPointNormalizer.nonperpendicularPoints_normalizer_image
      Q ρ φ hφ hρ a b (fun L => (hcounts L).1) (fun L => (hcounts L).2) hab⟩

theorem projective_normalizer_orthogonality (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ActionNormalizerOrthogonality Q (projectivePointAction Q) :=
  action_normalizer_orthogonality Q _ hQ hT (projective_action_properties Q hQ hT)

end FiniteGeometry

end CFSG.ComponentClassification.CatalogueBOrthogonalPointModelNormalizer
