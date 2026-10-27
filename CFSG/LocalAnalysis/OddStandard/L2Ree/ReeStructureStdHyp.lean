module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG.Open

theorem stdHyp_of_balanced {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L)
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hZ : center L = ⊥) : CFSG.EvenSporadicStandard.StdHyp G L where
  simple := hS.simple
  nonabelian := hS.nonab
  kProper := hS.kProper
  standard := hS.standard
  oddCore := hbal
  cyclicSylow := hcyc
  centerTwo := by rw [hZ]; exact IsPGroup.of_bot

theorem stdHyp_of_not_unbalanced {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hS : StandardSetting G L)
    (hbal : ¬ ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hZ : center L = ⊥) : CFSG.EvenSporadicStandard.StdHyp G L :=
  stdHyp_of_balanced hS (fun z hz => by
    by_contra h
    exact hbal ⟨z, hz, h⟩) hcyc hZ

end CFSG.OddStandard.L2Ree
