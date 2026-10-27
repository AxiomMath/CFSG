module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.LocalAnalysis.OddStandard.L2Ree.Common

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem exists_lieModel_of_classicalRep_or_exceptionalRep {G : Type} [Group G]
    (h : Milestones.ClassicalRep G ∨ ExceptionalRep G) :
    ∃ (τ : StatedLieTag) (n r f : ℕ), LieModel G τ n r f := by
  rcases h with ⟨t, n, p, f, hm⟩ | hex
  · refine ⟨t, n, p, f, .inl ⟨?_, hm⟩⟩
    rcases Milestones.statedClassicalModel_tag_mem _ t n p f hm with h | h | h | h | h | h <;>
      subst h <;> decide
  · rcases hex with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
    · exact ⟨t, 0, p, f, .inr (.inl ⟨rfl, ht, hm⟩)⟩
    · exact ⟨t, 0, p, f, .inr (.inr (.inl ⟨rfl, ht, hm⟩))⟩
    · exact ⟨.twistedB2, 0, p, f, .inr (.inr (.inr ⟨rfl, rfl, hm⟩))⟩

section Certified


theorem oddLieType_of_lieModel_of_standard {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.standardComponentIsStandard L) {τ : StatedLieTag} {n r f : ℕ}
    (hm : LieModel G τ n r f) : OddLieType G := by
  by_cases hr2 : r = 2
  · subst hr2
    obtain ⟨t, ht, ht2⟩ := hL.exists_involution_centralizer
    obtain ⟨-, hcomp⟩ := CFSG.OddStandard.L2Ree.isComponent_of_standard hL ht ht2
    exact (CFSG.ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType
      (S := G) ⟨τ, n, f, LieModel.admissible hm, hm⟩ t ht2 _ hcomp).elim
  · exact ⟨τ, n, r, f, (LieModel.admissible hm).1, hr2, LieModel.admissible hm, hm⟩

end Certified

end CFSG.OddStandard.SmallF3
