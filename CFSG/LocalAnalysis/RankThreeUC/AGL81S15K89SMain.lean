module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89SNorm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89SLThree
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1Main
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3Proved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankOneFinal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof

open CFSG.AGLEmbeddingD2.McLaughlin CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.ABGLocalTools

theorem K89Sp_of_inputs (hW : KFactThreeRankOneOvergroupL32) (hI : LThreeTwoCoreOdd)
    (hCat : CFSG.AGLEmbedding.CatalogOuterSolvable) (hF1 : KFactL32SimpleNormalizerAll)
    (hF2 : KFactL32OddFix) : K89Sp := by
  intro X _ _ hK N L hN hr hLN hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Y, hYL, hY⟩ := exists_Y L hL
  have hYN : Y ≤ N := hYL.trans hLN
  have hodd : ¬ 2 ∣ N.index := oddIndex_noChar hW hI X hK N hN hr Y hYN hY
  obtain ⟨S, hSN⟩ := exists_isSylowOf 2 N
  have hSle : S ≤ N := hSN.le
  have hSX : IsSylowOf 2 S ⊤ := by
    rw [isSylowOf_iff]
    obtain ⟨-, hSp, hSidx⟩ := isSylowOf_iff.mp hSN
    refine ⟨le_top, hSp, ?_⟩
    rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hSle]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
    · exact hSidx h
    · exact hodd h
  exact ⟨S, hSX, hSle, normalizer_le_of_spe hCat hF1 hF2 X hK N hN hr Y hYN hY S hSX hSle⟩

section Certificates

set_option linter.unusedSectionVars false


theorem K89Sp_of
    (hF1 : KFactL32SimpleNormalizer) (hF2 : KFactL32OddFix) : K89Sp := by
  have hCat : CFSG.AGLEmbedding.CatalogOuterSolvable := fun S _ _ _ hnab hcat =>
    CFSG.AGLEmbedding.kFactCatalogSchreier S ‹_› hnab hcat
  exact K89Sp_of_inputs
    (kFactThreeRankOneOvergroupL32_of_L3U3
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple
      overgroupL32L3_proved (overgroupL32U3_of_U3Odd overgroupL32U3Odd_proved))
    (lThreeTwoCoreOdd_of hCat) hCat
    (F1Proof.kFactL32SimpleNormalizerAll_of_families
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple hF1.1 hF1.2) hF2

end Certificates

end CFSG.LocalAnalysis.RankThreeUC.S15.K89SProof
