module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Fi22
public import CFSG.Sporadic.Bridge.Fi22Surj
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem presentation_eq : SporadicName.Fi22.presentation = Sporadic.fi22Presentation := rfl

theorem nonempty_mulEquiv_carrier_Fi22
    [IsSimpleGroup SporadicName.Fi22.Group] :
    Nonempty (SporadicName.Fi22.Group ≃* Blueprint.NativeSporadic.Carrier .Fi22) := by
  have : Nontrivial CFSG.Sporadic.Fi22.J :=
    nontrivial_of_two_le_natCard (k := 64561751654400) (by norm_num)
      (le_of_eq CFSG.Sporadic.Fi22.card_J.symm)
  obtain ⟨e⟩ := nonempty_mulEquiv_of_relators_two SporadicName.Fi22.presentation
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.Fi22.generatorCount_eq)
    (by rw [presentation_eq]; exact CFSG.Sporadic.Bridge.Fi22.relators_eval)
    CFSG.Sporadic.Fi22.closure_ab
  exact ⟨e.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm⟩

theorem tcExcludedSporadic_Fi22 :
    TCExcludedSporadic .Fi22 :=
  tcExcludedSporadic_of_equiv .Fi22 (T := Blueprint.NativeSporadic.Carrier .Fi22)
    (fun _ => nonempty_mulEquiv_carrier_Fi22) (by
      obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Fi22_elementary_three_rank_four
      exact ⟨E, hE, 4, by norm_num, hc⟩)

end CFSG.QuasithinUnique.SQTK
