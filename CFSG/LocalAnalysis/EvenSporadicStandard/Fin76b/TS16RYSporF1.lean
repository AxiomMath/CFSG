module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1J2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYF1J3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Sporadic.Schreier CFSG.Blueprint.NativeSporadic

theorem s16F1_of_sporadic
    {G : Type} [Group G] {L : Subgroup G} (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    S16F1 ↥L := by
  rcases hJ with hL | hL
  · obtain ⟨eL⟩ := hL
    exact S16F1.of_mulEquiv (eL.trans j2PermEquiv).symm J2.s16F1_j2P
  · obtain ⟨eL⟩ := hL
    exact S16F1.of_mulEquiv (eL.trans j3PermEquiv).symm J3.s16F1_j3P

end CFSG.EvenSporadicStandard.Fin76b
