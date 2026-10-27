module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.Sporadic.Bridge.J3Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.J3.presentation = Sporadic.j3Presentation := rfl

theorem nonempty_mulEquiv_carrier_J3
    [IsSimpleGroup SporadicName.J3.Group] :
    Nonempty (SporadicName.J3.Group ≃* Blueprint.NativeSporadic.Carrier .J3) := by
  have : Nontrivial (CFSG.Sporadic.J3.J CFSG.Sporadic.J3.Native.j3Data) :=
    nontrivial_of_two_le_natCard (by norm_num) CFSG.Sporadic.Bridge.J3.le_card_J
  obtain ⟨e⟩ := nonempty_mulEquiv_of_relators_two SporadicName.J3.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.J3.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.J3.relators_eval)
    (CFSG.Sporadic.J3.closure_ab CFSG.Sporadic.J3.Native.j3Data)
  exact ⟨e.trans CFSG.Sporadic.Bridge.J3.nativeEquiv.symm⟩

end CFSG.QuasithinUnique.SQTK
