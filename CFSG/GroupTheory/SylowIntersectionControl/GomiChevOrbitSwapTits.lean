module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTits
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevTwoAtoms
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoAssembly

public section

namespace CFSG.GroupTheory

theorem gomiAtomsFixed_of_lie_tits
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : GomiAtomsFixed K := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  have hmodel := CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := K) ⟨hv, ⟨e⟩⟩
  obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 1 hmodel
  exact gomiAtomsFixed_of_twoPar_card_ne e'
    (CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.twoParLat_tits).toTwoPar
    (by rw [CFSG.Sporadic.Schreier.Tits.card_titsPointStab,
      CFSG.Sporadic.Schreier.Tits.card_titsLineStab]; decide)

end CFSG.GroupTheory
