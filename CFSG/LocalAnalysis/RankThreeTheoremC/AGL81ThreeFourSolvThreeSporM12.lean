module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeCoreE1
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreE1Mathieu
import CFSG.LocalAnalysis.AGLEmbeddingD2.DatumSup
import CFSG.Sporadic.Bridge.M12
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Mathieu

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Blueprint


theorem threeFourSolvThreeNoneAt_m12 :
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.sporadic .M12).Group := by
  refine ThreeFourSolvThreeNoneAt.of_coreE1 fun L _ _ he => ?_
  obtain ⟨e⟩ := he
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have f : L ≃* ↥NativeSporadic.M12 := e.trans eC.symm
  haveI : IsSimpleGroup ↥NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  refine ⟨f.isSimpleGroup, ?_, fun T => ?_,
    CFSG.AGLEmbedding.CoreE1.Datum.of_mulEquiv f CFSG.AGLEmbedding.coreE1Datum_M12⟩
  · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence f).toEquiv,
      CFSG.ComponentClassification.M12Cover.card_outer]
    norm_num
  ·
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set S : Sylow 3 ↥NativeSporadic.M12 := T.mapSurjective (f := f.toMonoidHom) f.surjective
      with hSdef
    have h := CFSG.AGLEmbeddingD2.glbCore_map_le_of_mulEquiv Nat.prime_three 2 f.symm
      (S : Subgroup ↥NativeSporadic.M12)
    have hS : CFSG.Open.GLBCore 3 2 (S : Subgroup ↥NativeSporadic.M12) = ⊤ :=
      CFSG.AGLEmbedding.glbCore_M12_three S
    rw [hS, Subgroup.map_top_of_surjective _ f.symm.surjective, top_le_iff] at h
    have hST : (S : Subgroup ↥NativeSporadic.M12).map f.symm.toMonoidHom = (T : Subgroup L) := by
      ext x
      simp [hSdef, Sylow.coe_mapSurjective]
    rwa [hST] at h

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
