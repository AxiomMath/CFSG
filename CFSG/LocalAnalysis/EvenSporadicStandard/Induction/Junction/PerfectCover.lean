module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction.Hyp

theorem isQuasisimple_of_perfect_cover {A B : Type*} [Group A] [Group B] (hA : Group.IsPerfect A)
    (hB : CFSG.IsQuasisimple B) (π : A →* B) (hπ : Function.Surjective π)
    (hker : π.ker ≤ center A) : CFSG.IsQuasisimple A := by
  obtain ⟨e⟩ := cqEquiv_of_cover π hπ hker
  refine ⟨hA, ?_, ?_⟩
  · have := hB.2.1
    exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hB.2.2
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa [map_mul] using this

end CFSG.EvenSporadicStandard.Induction.Junction
