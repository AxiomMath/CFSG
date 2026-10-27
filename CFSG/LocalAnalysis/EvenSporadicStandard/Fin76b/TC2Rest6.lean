module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.RootFacts
public import CFSG.Sporadic.Schreier.PairJ3Faithful

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

@[expose] def OuterSylowFacts {G : Type} [Group G] (z : G) (E S : Subgroup G) : Prop :=
  ((∃ k : ℕ, 2 ≤ k ∧ Nonempty (S ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (S ≃* CFSG.Open.SemidihedralGroup n)) ∧
    (∀ k : ℕ, 2 ≤ k → Nonempty (S ≃* DihedralGroup (2 ^ k)) →
      ∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
        N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
        (N : Set (centralizer (E : Set G))) *
          (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) =
            Set.univ) ∧
    (∀ g : G, g * z * g⁻¹ ∈ S → ∃ s ∈ S, g * z * g⁻¹ = s * z * s⁻¹)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem rootFactsClass_of_sporadic
    (hRJ2 : RootFactsClass ↥ComponentClassification.J2Cover.Models.P)
    (hRJ3 : RootFactsClass ↥j3P) (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    RootFactsClass ↥L := by
  rcases hJ with hL | hL
  · obtain ⟨e⟩ := hL
    exact RootFactsClass.of_mulEquiv
      ((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
        (ComponentClassification.J2Cover.nativeEquivP.symm.trans e.symm)) hRJ2
  · obtain ⟨e⟩ := hL
    exact RootFactsClass.of_mulEquiv (e.trans j3PermEquiv).symm hRJ3

end CFSG.EvenSporadicStandard.Fin76b
