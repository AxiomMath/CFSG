module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16J2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16J3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Sporadic.Schreier CFSG.Blueprint.NativeSporadic

theorem elAb16_mulAut_of_isSporadic
    {G : Type} [Group G] {L : Subgroup G}
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) : ElAb16 (MulAut ↥L) := by
  rcases hJ with hL | hL
  · obtain ⟨eL⟩ := hL
    exact ElAb16.of_mulEquiv (MulAut.congr (eL.trans j2PermEquiv)) elAb16_mulAut_j2P
  · obtain ⟨eL⟩ := hL
    exact ElAb16.of_mulEquiv (MulAut.congr (eL.trans j3PermEquiv)) elAb16_mulAut_j3P

end CFSG.EvenSporadicStandard.Fin76b
