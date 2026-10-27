module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuous
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSmallA6U33
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuousTwoPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

theorem gomiAtomsOnlyTop_of_psu_three_three
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.StatedClassicalModel K .PSU 3 3 1) :
    GomiAtomsOnlyTop K := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hK⟩)
  obtain ⟨_, P₁, P₂, h⟩ := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.twoPar_u33
  obtain ⟨P₁', P₂', h'⟩ := h.exists_of_equiv e.symm
    (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow (default : Sylow 2 K))
  exact gomiAtomsOnlyTop_of_twoPar h'

end CFSG.GroupTheory
