module

public import CFSG.GH74.E2.ComponentsShape
public import CFSG.GH74.E2.ComponentsUnique
public import CFSG.GH74.E2.EvenLie

public section

namespace CFSG.GH74.E2

open Subgroup Blueprint CFSG.GH74.Generic

theorem evenLieRankFour :
    EvenLieRankFour :=
  fun _ _ _ hs hnab he h4 => even_lie_rank_le_four hs hnab he h4

theorem evenType_components
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) (hD : K0Data) :
    ComponentList := by
  intro G _ _ hH t ht K hK
  have hshape : ∀ L : Subgroup G, IsCompCen t L → K0Shape ↥L := by
    intro L hL
    obtain ⟨⟨hq, hZ, hS, hne⟩, hres⟩ := isCompCen_inC2 hH ht hL
    have hZ2 : IsPGroup 2 ↥(center ↥L) := by
      rw [hZ]
      exact CFSG.pCore_isPGroup
    exact k0Shape_of_component hG hF evenLieRankFour
      ⟨hq, hZ2, hne, isCompCen_gen4 hH L, isCompCen_rank hH ht hL, hres⟩ hS
  refine ⟨hshape K hK, fun K' hK' => ?_⟩
  by_contra hne
  exact false_of_two_components hH hD ht hK hK' (hshape K hK) (hshape K' hK') (Ne.symm hne)

end CFSG.GH74.E2
