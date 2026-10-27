module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYJ3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Sporadic.Schreier CFSG.Blueprint.NativeSporadic

theorem s16ModelClass_of_sporadic
    {G : Type} [Group G] {L : Subgroup G} (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    S16ModelClass ↥L := by
  rcases hJ with hL | hL
  · obtain ⟨eL⟩ := hL
    exact S16ModelClass.of_mulEquiv (eL.trans j2PermEquiv).symm J2.s16ModelClass_j2P
  · obtain ⟨eL⟩ := hL
    exact S16ModelClass.of_mulEquiv (eL.trans j3PermEquiv).symm J3.s16ModelClass_j3P

end CFSG.EvenSporadicStandard.Fin76b
