module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.Sporadic.Bridge.HSSurj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.HS.presentation = Sporadic.hsPresentation := rfl

theorem nonempty_mulEquiv_carrier_HS
    [IsSimpleGroup SporadicName.HS.Group] :
    Nonempty (SporadicName.HS.Group ≃* Blueprint.NativeSporadic.Carrier .HS) := by
  have : Nontrivial CFSG.Sporadic.Bridge.HS.JD :=
    nontrivial_of_two_le_natCard (by norm_num) CFSG.Sporadic.Bridge.HS.le_card_J
  obtain ⟨e⟩ := nonempty_mulEquiv_of_relators_two SporadicName.HS.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.HS.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.HS.relators_eval)
    (CFSG.Sporadic.SmallF2.closure_ab CFSG.Sporadic.HS.Native.hsData)
  exact ⟨e.trans CFSG.Sporadic.Bridge.HS.nativeEquiv.symm⟩

end CFSG.QuasithinUnique.SQTK
