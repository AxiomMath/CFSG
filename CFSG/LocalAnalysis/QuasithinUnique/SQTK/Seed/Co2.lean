module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.Sporadic.Bridge.Co2Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.Co2.presentation = Sporadic.co2Presentation := rfl

theorem nonempty_mulEquiv_carrier_Co2
    [IsSimpleGroup SporadicName.Co2.Group] :
    Nonempty (SporadicName.Co2.Group ≃* Blueprint.NativeSporadic.Carrier .Co2) := by
  have : Nontrivial CFSG.Sporadic.Bridge.Co2.JD :=
    nontrivial_of_two_le_natCard (by norm_num) CFSG.Sporadic.Bridge.Co2.le_card_J
  obtain ⟨e⟩ := nonempty_mulEquiv_of_relators_two SporadicName.Co2.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.Co2.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.Co2.relators_eval)
    (CFSG.Sporadic.SmallF2.closure_ab CFSG.Sporadic.Co2.Native.co2Data)
  exact ⟨e.trans CFSG.Sporadic.Bridge.Co2.nativeEquiv.symm⟩

end CFSG.QuasithinUnique.SQTK
