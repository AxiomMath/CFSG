module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.Sporadic.Bridge.HeSurj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.He.presentation = Sporadic.hePresentation := rfl

theorem nonempty_mulEquiv_carrier_He
    [IsSimpleGroup SporadicName.He.Group] :
    Nonempty (SporadicName.He.Group ≃* Blueprint.NativeSporadic.Carrier .He) := by
  have : Nontrivial CFSG.Sporadic.He.J :=
    nontrivial_of_two_le_natCard (k := 4030387200) (by norm_num)
      (le_of_eq CFSG.Sporadic.He.card_J.symm)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_relators_two SporadicName.He.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.He.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.He.relators_eval)
    CFSG.Sporadic.He.closure_ab
  exact ⟨e.trans CFSG.Sporadic.He.heEquivJ.symm⟩

end CFSG.QuasithinUnique.SQTK
