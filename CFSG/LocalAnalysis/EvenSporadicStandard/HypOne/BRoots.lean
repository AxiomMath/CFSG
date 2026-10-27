module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.BGeneric

public section

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup CFSG.ComponentClassification.M12Cover

theorem noNormalFour_centralizer_of_roots {Y : Type*} [Group Y] (a : Y)
    (hcen : ∀ z : Y, z * z = 1 → (∀ y : Y, y * a = a * y → z * y = y * z) → z = 1 ∨ z = a)
    (h : ∀ n : centralizer ({a} : Set Y), (n : Y) * n = a →
      5 ≤ Nat.card {y : centralizer ({a} : Set Y) // IsConj n y}) :
    NoNormalFour (centralizer ({a} : Set Y)) := by
  have hmem : a ∈ centralizer ({a} : Set Y) :=
    mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff] at hg; rw [hg]
  refine noNormalFour_of_root_class_large (⟨a, hmem⟩ : centralizer ({a} : Set Y))
    (fun z hz2 hzc => ?_) (fun n hn => h n ?_)
  · have hz2' : (z : Y) * (z : Y) = 1 := by
      have := congrArg Subtype.val hz2
      simpa using this
    rcases hcen (z : Y) hz2' (fun y hy => by
      have h1 := hzc ⟨y, mem_centralizer_singleton_iff.2 hy⟩
      simpa using congrArg Subtype.val h1) with h1 | h1
    · left
      exact Subtype.ext h1
    · right
      exact Subtype.ext h1
  · have := congrArg Subtype.val hn
    simpa using this

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
