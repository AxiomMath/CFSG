module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuous
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSmallA6U33
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuousTwoPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

theorem gomiAtomsOnlyTop_of_mulEquiv_alternatingGroup_six
    {K : Type} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin 6)) : GomiAtomsOnlyTop K := by
  obtain ⟨_, P₁, P₂, h⟩ := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.twoPar_alt_six
  obtain ⟨P₁', P₂', h'⟩ := h.exists_of_equiv e.symm
    (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow (default : Sylow 2 K))
  exact gomiAtomsOnlyTop_of_twoPar h'

end CFSG.GroupTheory
