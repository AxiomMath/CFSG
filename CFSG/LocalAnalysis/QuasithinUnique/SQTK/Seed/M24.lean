module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.Sporadic.Bridge.M24Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.M24.presentation = Sporadic.m24Presentation := rfl

theorem nonempty_mulEquiv_carrier_M24
    [IsSimpleGroup SporadicName.M24.Group] :
    Nonempty (SporadicName.M24.Group ≃* Blueprint.NativeSporadic.Carrier .M24) := by
  have : Nontrivial (Blueprint.NativeSporadic.Carrier .M24) :=
    nontrivial_of_two_le_natCard (k := 244823040) (by norm_num)
      (le_of_eq CFSG.Sporadic.Mathieu.card_M24.symm)
  exact nonempty_mulEquiv_of_relators_two SporadicName.M24.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.M24.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.M24.relators_eval)
    CFSG.Sporadic.Bridge.M24.closure_gen

end CFSG.QuasithinUnique.SQTK
