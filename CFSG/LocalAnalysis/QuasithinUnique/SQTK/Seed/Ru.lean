module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.Sporadic.Bridge.RuSurj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.Ru.presentation = Sporadic.ruPresentation := rfl

private theorem seedEquiv_aux
    (P : GroupPresentation) (hP : P = Sporadic.ruPresentation)
    [IsSimpleGroup P.Group] : Nonempty (P.Group ≃* Blueprint.NativeSporadic.Carrier .Ru) := by
  subst hP
  have : Nontrivial (CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Ru.Native.ruData) :=
    nontrivial_of_two_le_natCard (k := 145926144000) (by norm_num)
      (le_of_eq CFSG.Sporadic.Bridge.Ru.card_J.symm)
  exact ⟨(mulEquivOfSurjective _ (CFSG.Sporadic.Bridge.Ru.presHom_surjective
    CFSG.Sporadic.Bridge.Ru.bridge_facts.1)).trans
    CFSG.Sporadic.Bridge.Ru.nativeEquiv.symm⟩

theorem nonempty_mulEquiv_carrier_Ru
    [IsSimpleGroup SporadicName.Ru.Group] :
    Nonempty (SporadicName.Ru.Group ≃* Blueprint.NativeSporadic.Carrier .Ru) :=
  seedEquiv_aux SporadicName.Ru.presentation presentation_eq

end CFSG.QuasithinUnique.SQTK
