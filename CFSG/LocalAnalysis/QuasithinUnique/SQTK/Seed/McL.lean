module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.Sporadic.Bridge.McLSurj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

private theorem presentation_eq : SporadicName.McL.presentation = Sporadic.mclPresentation := rfl

theorem nonempty_mulEquiv_carrier_McL
    [IsSimpleGroup SporadicName.McL.Group] :
    Nonempty (SporadicName.McL.Group ≃* Blueprint.NativeSporadic.Carrier .McL) := by
  have : Nontrivial CFSG.Sporadic.McL.J :=
    nontrivial_of_two_le_natCard (k := 898128000) (by norm_num)
      (le_of_eq CFSG.Sporadic.McL.card_J.symm)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_relators_two SporadicName.McL.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.McL.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.McL.relators_eval)
    CFSG.Sporadic.McL.closure_ab
  exact ⟨e.trans CFSG.Sporadic.McL.mclEquivJ.symm⟩

theorem tcExcludedSporadic_McL :
    TCExcludedSporadic .McL :=
  tcExcludedSporadic_of_equiv .McL (T := Blueprint.NativeSporadic.Carrier .McL)
    (fun _ => nonempty_mulEquiv_carrier_McL) (by
      obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.McL_elementary_three_rank_four
      exact ⟨E, hE, 4, by norm_num, hc⟩)

end CFSG.QuasithinUnique.SQTK
