module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTwoAtoms
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParSmallA6U33

public section

namespace CFSG.GroupTheory

theorem gomiAtomOrbitTop_of_mulEquiv_alternatingGroup_six
    {K : Type} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin 6)) : GomiAtomOrbitTop K := by
  obtain ⟨T, P₁, P₂, h⟩ := AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.twoPar_alt_six
  exact gomiAtomOrbitTop_of_twoPar e h

end CFSG.GroupTheory
