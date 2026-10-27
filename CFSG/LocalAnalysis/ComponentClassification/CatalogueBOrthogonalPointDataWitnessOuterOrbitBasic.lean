module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbitFull
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBStabilizerFamilyQuotient

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CatalogueBStabilizerFamily
open scoped Pointwise

universe u v

variable {G : Type u} [Group G] {X : Type v}

theorem family_eq_conjugacy_of_transitive (rho : G →* Equiv.Perm X) (x : X)
    (htrans : ∀ y : X, ∃ g : G, rho g x = y) :
    family rho =
      CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily (pointStabilizer rho x) := by
  ext U
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨g, hg⟩ := htrans y
    refine ⟨g, ?_⟩
    change (pointStabilizer rho x).map (MulAut.conj g).toMonoidHom = pointStabilizer rho y
    rw [pointStabilizer_conj, hg]
  · rintro ⟨g, rfl⟩
    exact ⟨rho g x, (pointStabilizer_conj rho g x).symm⟩

theorem familyAut_eq_conjugacyStabilizer (rho : G →* Equiv.Perm X) (x : X)
    (hfamily : family rho =
      CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily (pointStabilizer rho x)) :
    familyAut rho =
      CatalogueBOrthogonalSmallFamilyOrbit.familyStabilizer (pointStabilizer rho x) :=
  congrArg (MulAction.stabilizer (MulAut G)) hfamily

@[expose] def familyConjugacyOuterEquiv (rho : G →* Equiv.Perm X) (x : X)
    (hfamily : family rho =
      CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily (pointStabilizer rho x)) :
    familyOuter rho ≃*
      CatalogueBOrthogonalSmallFamilyOrbit.FamilyOuter (pointStabilizer rho x) := by
  let _ : ((MulAut.conj : G →* MulAut G).range.subgroupOf (familyAut rho)).Normal :=
    familyInnerNormal rho
  let _ : ((OuterAutomorphisms.inner G).subgroupOf
      (CatalogueBOrthogonalSmallFamilyOrbit.familyStabilizer (pointStabilizer rho x))).Normal :=
    CatalogueBOrthogonalSmallFamilyOrbit.familyInnerNormal (pointStabilizer rho x)
  exact QuotientGroup.equivQuotientSubgroupOfOfEq
    (A' := (MulAut.conj : G →* MulAut G).range) (A := familyAut rho)
    (B' := OuterAutomorphisms.inner G)
    (B := CatalogueBOrthogonalSmallFamilyOrbit.familyStabilizer (pointStabilizer rho x))
    rfl (familyAut_eq_conjugacyStabilizer rho x hfamily)

theorem familyConjugacyOuterEquiv_mk (rho : G →* Equiv.Perm X) (x : X)
    (hfamily : family rho =
      CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily (pointStabilizer rho x))
    (alpha : familyAut rho) :
    familyConjugacyOuterEquiv rho x hfamily ((QuotientGroup.mk' (familyInner rho)) alpha) =
      (QuotientGroup.mk'
        (CatalogueBOrthogonalSmallFamilyOrbit.familyInner (pointStabilizer rho x)))
        (Subgroup.inclusion (familyAut_eq_conjugacyStabilizer rho x hfamily).le alpha) :=
  rfl

theorem familyConjugacyOuter_derived_eq_bot (rho : G →* Equiv.Perm X) (x : X)
    (hfamily : family rho =
      CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily (pointStabilizer rho x))
    (d : ℕ) (hd : derivedSeries (familyOuter rho) d = ⊥) :
    derivedSeries
      (CatalogueBOrthogonalSmallFamilyOrbit.FamilyOuter (pointStabilizer rho x)) d = ⊥ := by
  rw [← map_derivedSeries_eq (f := (familyConjugacyOuterEquiv rho x hfamily).toMonoidHom)
    (familyConjugacyOuterEquiv rho x hfamily).surjective d, hd, Subgroup.map_bot]

theorem outer_derived_eq_bot_of_small_point_family [Finite G]
    (rho : G →* Equiv.Perm X) (x : X)
    (hfamily : family rho =
      CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily (pointStabilizer rho x))
    (d : ℕ) (hd : derivedSeries (familyOuter rho) d = ⊥)
    (hO : Nat.card
      (CatalogueBOrthogonalSmallFamilyOrbit.FamilyOrbit (pointStabilizer rho x)) ≤ 3) :
    derivedSeries (OuterAutomorphisms.Outer G) (d + 2) = ⊥ :=
  CatalogueBOrthogonalSmallFamilyOrbit.orthogonal_geometry_small_family_orbit_solvability
    (pointStabilizer rho x) d (familyConjugacyOuter_derived_eq_bot rho x hfamily d hd) hO

theorem familyOrbit_card_one_of_familyAut_top (rho : G →* Equiv.Perm X) (x : X)
    (hfamily : family rho =
      CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily (pointStabilizer rho x))
    (htop : familyAut rho = ⊤) :
    Nat.card (CatalogueBOrthogonalSmallFamilyOrbit.FamilyOrbit (pointStabilizer rho x)) = 1 := by
  let : Unique
      (CatalogueBOrthogonalSmallFamilyOrbit.FamilyOrbit (pointStabilizer rho x)) := {
    default := CatalogueBOrthogonalSmallFamilyOrbit.familyOrbitBase (pointStabilizer rho x)
    uniq := by
      intro F'
      apply Subtype.ext
      obtain ⟨alpha, halpha⟩ := MulAction.mem_orbit_iff.mp F'.property
      rw [← halpha]
      have ha : alpha ∈
          CatalogueBOrthogonalSmallFamilyOrbit.familyStabilizer (pointStabilizer rho x) := by
        rw [← familyAut_eq_conjugacyStabilizer rho x hfamily, htop]
        exact Subgroup.mem_top alpha
      exact ha }
  exact Nat.card_unique

theorem outer_derived_eq_bot_of_point_family_top [Finite G]
    (rho : G →* Equiv.Perm X) (x : X)
    (hfamily : family rho =
      CatalogueBOrthogonalSmallFamilyOrbit.conjugacyFamily (pointStabilizer rho x))
    (d : ℕ) (hd : derivedSeries (familyOuter rho) d = ⊥) (htop : familyAut rho = ⊤) :
    derivedSeries (OuterAutomorphisms.Outer G) d = ⊥ :=
  CatalogueBOrthogonalSmallFamilyOrbit.orthogonal_geometry_singleton_family_orbit_solvability
    (pointStabilizer rho x) d (familyConjugacyOuter_derived_eq_bot rho x hfamily d hd)
    (familyOrbit_card_one_of_familyAut_top rho x hfamily htop)

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
