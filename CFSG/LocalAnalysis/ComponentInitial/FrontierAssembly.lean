module

public import CFSG.LocalAnalysis.ComponentInitial.FrontierUniversalSelection
public import CFSG.LocalAnalysis.ComponentInitial.BlockAschbacherTheorem5
public import CFSG.LocalAnalysis.ComponentInitial.KProperLocalBPumpUp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem initial_standard_component_frontier_of_schreierFor {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X) (hS : SchreierFor C)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper C G)
    (hrank : 3 ≤ CFSG.Assembly.twoRank G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    (∃ t : G, orderOf t = 2 ∧ ∃ L : Subgroup G,
        CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
          CFSG.Assembly.ComponentType.IsStandardSubgroup L) ∨
      (∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G,
        CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)) ∧ z ∈ J ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ S : Sylow 2 J,
            Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) := by
  rcases frontier_universal_selection hC (kProper_ordinary_local_B_pump_up hS) G hnonab hK hrank
      hcomp hB with h | h | ⟨a, ha, J, hJ, hq, hr, hev, hu⟩
  · exact Or.inl h
  · exact Or.inr h
  · have hr' : 2 ≤ CFSG.Assembly.pRank 2 J := by
      rw [← FrontierUniversalSelection.pRank_eq_assembly_pRank]
      exact hr
    exact Or.inl ⟨a, ha, J, hJ,
      universal_rank_two_component_isStandardSubgroup hnonab hq hr' hev hu⟩

theorem initial_standard_component_frontier_of_tits_sporadic
    (hTits : ∀ (S : Type) [Group S] (p f : ℕ), CFSG.Blueprint.ReeTitsModel S .Tits p f →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))
    (hspor : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      CFSG.Blueprint.NativeSporadic.SporadicRep S →
        Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer S))
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hrank : 3 ≤ CFSG.Assembly.twoRank G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    (∃ t : G, orderOf t = 2 ∧ ∃ L : Subgroup G,
        CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
          CFSG.Assembly.ComponentType.IsStandardSubgroup L) ∨
      (∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G,
        CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({z} : Set G)) ∧ z ∈ J ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ S : Sylow 2 J,
            Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :=
  initial_standard_component_frontier_of_schreierFor
    (fun e h => CFSG.SectionRank.catalog_of_mulEquiv e h)
    (fun X _ _ _ hX hcat =>
      CFSG.ComponentClassification.CatalogueSchreierAssembly.catalog_schreier_of_tits_sporadic hX
        (hTits X) (hspor X hX) hcat)
    G hnonab hK hrank hcomp hB

end CFSG.LocalAnalysis.ComponentInitial
