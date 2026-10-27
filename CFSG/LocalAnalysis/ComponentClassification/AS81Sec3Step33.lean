module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Points

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

section Step33

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
  {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U : Subgroup G}

theorem P_le_X (hSz : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y) :
    P ≤ normalizer (E : Set G) ⊓ normalizer ((zpowers x : Subgroup G) : Set G) := by
  intro p hp
  have hp' : p ∈ sec3B A₁ x ⊓ normalizer (E : Set G) := by
    rw [hSz.P_eq] at hp
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _ hp
  refine ⟨hp'.2, centralizer_le_normalizer _ ?_⟩
  rw [Sec3.centralizer_zpowers]
  exact (map_subtype_le _ : sec3B A₁ x ≤ centralizer ({x} : Set G)) hp'.1

end Step33

end CFSG.ComponentClassification.AS81
