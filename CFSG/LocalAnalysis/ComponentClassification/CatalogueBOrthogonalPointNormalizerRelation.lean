module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointNormalizerBasic

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointNormalizer

open CatalogueBOrthogonalPointAction
open scoped Classical

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V)
variable {G : Type w} [Group G]
variable (ρ : G →* Equiv.Perm (Points Q)) (φ : Equiv.Perm (Points Q))

theorem pointPerp_normalizer_of_orbit_counts [Finite (Points Q)]
    (hφ : φ ∈ Subgroup.normalizer ρ.range)
    (hOrbits : ∀ L M : Points Q, actionStabilizerOrbit Q ρ L M =
      if M = L then {L} else if PointPerp L M then perpendicularPoints Q L
      else nonperpendicularPoints Q L)
    (a b : ℕ)
    (ha : ∀ L : Points Q, Nat.card (perpendicularPoints Q L) = a)
    (hb : ∀ L : Points Q, Nat.card (nonperpendicularPoints Q L) = b)
    (hab : a ≠ b) (L M : Points Q) (hLM : PointPerp L M) :
    PointPerp (φ L) (φ M) := by
  by_cases hML : M = L
  · subst M
    exact pointPerp_self Q (φ L)
  by_contra hφLM
  have hφML : φ M ≠ φ L := fun h => hML (φ.injective h)
  have hcard := actionStabilizerOrbit_normalizer_card Q ρ φ hφ L M
  rw [hOrbits L M, ite_eq_right hML, ite_eq_left hLM,
    hOrbits (φ L) (φ M), ite_eq_right hφML, ite_eq_right hφLM] at hcard
  exact hab ((ha L).symm.trans (hcard.trans (hb (φ L))))

theorem pointPerp_normalizer_iff_of_orbit_counts [Finite (Points Q)]
    (hφ : φ ∈ Subgroup.normalizer ρ.range)
    (hOrbits : ∀ L M : Points Q, actionStabilizerOrbit Q ρ L M =
      if M = L then {L} else if PointPerp L M then perpendicularPoints Q L
      else nonperpendicularPoints Q L)
    (a b : ℕ)
    (ha : ∀ L : Points Q, Nat.card (perpendicularPoints Q L) = a)
    (hb : ∀ L : Points Q, Nat.card (nonperpendicularPoints Q L) = b)
    (hab : a ≠ b) (L M : Points Q) :
    PointPerp (φ L) (φ M) ↔ PointPerp L M := by
  constructor
  · intro h
    have hinv : φ⁻¹ ∈ Subgroup.normalizer ρ.range :=
      (Subgroup.normalizer (ρ.range : Set (Equiv.Perm (Points Q)))).inv_mem (x := φ) hφ
    have hback := pointPerp_normalizer_of_orbit_counts Q ρ φ⁻¹ hinv
      hOrbits a b ha hb hab (φ L) (φ M) h
    change PointPerp (φ.symm (φ L)) (φ.symm (φ M)) at hback
    simpa only [φ.symm_apply_apply] using hback
  · exact pointPerp_normalizer_of_orbit_counts Q ρ φ hφ hOrbits a b ha hb hab L M

theorem pointPerp_normalizer_iff [Finite (Points Q)]
    (hφ : φ ∈ Subgroup.normalizer ρ.range) (hρ : ActionProperties Q ρ)
    (a b : ℕ)
    (ha : ∀ L : Points Q, Nat.card (perpendicularPoints Q L) = a)
    (hb : ∀ L : Points Q, Nat.card (nonperpendicularPoints Q L) = b)
    (hab : a ≠ b) (L M : Points Q) :
    PointPerp (φ L) (φ M) ↔ PointPerp L M := by
  obtain ⟨_, _, _, _, _, _, hOrbits, _⟩ := hρ
  exact pointPerp_normalizer_iff_of_orbit_counts Q ρ φ hφ hOrbits a b ha hb hab L M

theorem perpendicularPoints_normalizer_image [Finite (Points Q)]
    (hφ : φ ∈ Subgroup.normalizer ρ.range) (hρ : ActionProperties Q ρ)
    (a b : ℕ)
    (ha : ∀ L : Points Q, Nat.card (perpendicularPoints Q L) = a)
    (hb : ∀ L : Points Q, Nat.card (nonperpendicularPoints Q L) = b)
    (hab : a ≠ b) (L : Points Q) :
    φ '' perpendicularPoints Q L = perpendicularPoints Q (φ L) := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    change φ Y ≠ φ L ∧ PointPerp (φ L) (φ Y)
    exact ⟨fun h => hY.1 (φ.injective h),
      (pointPerp_normalizer_iff Q ρ φ hφ hρ a b ha hb hab L Y).mpr hY.2⟩
  · intro hX
    change X ≠ φ L ∧ PointPerp (φ L) X at hX
    refine ⟨φ.symm X, ?_, φ.apply_symm_apply X⟩
    change φ.symm X ≠ L ∧ PointPerp L (φ.symm X)
    constructor
    · intro h
      apply hX.1
      rw [← φ.apply_symm_apply X, h]
    · apply (pointPerp_normalizer_iff Q ρ φ hφ hρ a b ha hb hab L (φ.symm X)).mp
      simpa only [φ.apply_symm_apply] using hX.2

theorem nonperpendicularPoints_normalizer_image [Finite (Points Q)]
    (hφ : φ ∈ Subgroup.normalizer ρ.range) (hρ : ActionProperties Q ρ)
    (a b : ℕ)
    (ha : ∀ L : Points Q, Nat.card (perpendicularPoints Q L) = a)
    (hb : ∀ L : Points Q, Nat.card (nonperpendicularPoints Q L) = b)
    (hab : a ≠ b) (L : Points Q) :
    φ '' nonperpendicularPoints Q L = nonperpendicularPoints Q (φ L) := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    change ¬ PointPerp (φ L) (φ Y)
    exact fun h => hY ((pointPerp_normalizer_iff Q ρ φ hφ hρ a b ha hb hab L Y).mp h)
  · intro hX
    change ¬ PointPerp (φ L) X at hX
    refine ⟨φ.symm X, ?_, φ.apply_symm_apply X⟩
    change ¬ PointPerp L (φ.symm X)
    intro h
    apply hX
    have hforward :=
      (pointPerp_normalizer_iff Q ρ φ hφ hρ a b ha hb hab L (φ.symm X)).mpr h
    simpa only [φ.apply_symm_apply] using hforward

end CFSG.ComponentClassification.CatalogueBOrthogonalPointNormalizer
