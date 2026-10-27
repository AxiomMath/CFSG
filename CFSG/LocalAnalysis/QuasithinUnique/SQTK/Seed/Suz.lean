module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.Sporadic.Bridge.SuzSurj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.Suz.presentation = Sporadic.suzPresentation := rfl

private theorem seedEquiv_aux
    (P : GroupPresentation) (hP : P = Sporadic.suzPresentation)
    [IsSimpleGroup P.Group] : Nonempty (P.Group ≃* Blueprint.NativeSporadic.Carrier .Suz) := by
  subst hP
  have : Nontrivial CFSG.Sporadic.Suz.J :=
    nontrivial_of_two_le_natCard (k := 448345497600) (by norm_num)
      (le_of_eq CFSG.Sporadic.Suz.card_J.symm)
  exact ⟨(mulEquivOfSurjective CFSG.Sporadic.Bridge.Suz.toJ
    CFSG.Sporadic.Bridge.Suz.toJ_surjective).trans CFSG.Sporadic.Suz.suzEquivJ.symm⟩

theorem nonempty_mulEquiv_carrier_Suz
    [IsSimpleGroup SporadicName.Suz.Group] :
    Nonempty (SporadicName.Suz.Group ≃* Blueprint.NativeSporadic.Carrier .Suz) :=
  seedEquiv_aux SporadicName.Suz.presentation presentation_eq

end CFSG.QuasithinUnique.SQTK
