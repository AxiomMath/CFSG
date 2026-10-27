module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeCoreE1
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreE1Tits
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen


theorem threeFourSolvThreeNoneAt_tits (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits) :
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group := by
  refine ThreeFourSolvThreeNoneAt.of_coreE1 fun L _ _ he => ?_
  obtain ⟨e⟩ := he
  obtain ⟨eS⟩ : Nonempty (L ≃* ↥CFSG.Sporadic.Schreier.Tits.titsD) := by
    obtain ⟨⟨d', hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
    simp only at hd
    subst hd
    exact CFSG.Sporadic.Schreier.Tits.titsModelEquiv L 2 1
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
  haveI : IsSimpleGroup ↥CFSG.Sporadic.Schreier.Tits.titsD :=
    CFSG.Sporadic.Schreier.Tits.titsD_simple
  refine ⟨eS.isSimpleGroup, ?_, CFSG.AGLEmbeddingD2.kFactTitsThreeCore L d hd ⟨e⟩,
    CFSG.AGLEmbedding.CoreE1.Datum.of_mulEquiv eS CFSG.AGLEmbeddingD2.coreE1Datum_titsD⟩
  rw [CFSG.AGLEmbeddingD2.card_outer_tits_of_mulEquiv d hd e]
  norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
