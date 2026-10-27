module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HJ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HJ3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

theorem fin76bEFacts613 :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
      (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
      EFacts613 E t := by
  intro G _ _ L z t T₀ E Q x β B hconf
  rcases hconf.sporadic with hL | hL
  · exact J2.eFacts613_of_isSporadic hconf.cfg hconf.econfig hL
  · exact J3.eFacts613_of_isSporadic hconf.cfg hconf.econfig hL

end CFSG.EvenSporadicStandard.Fin76b
