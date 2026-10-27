module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.MonsterRowsData
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenRank

public section

namespace CFSG.AGLEmbedding.Norton.OrdinaryProofs

open CFSG.Open CFSG.Monster.Generated
open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)

theorem sup_thirteen_of_core_two
    (c13 : ∀ S : Sylow 13 Gmat, GLBCore 13 2 (S : Subgroup Gmat) = ⊤) :
    ∀ S : Sylow 13 Gmat, ∀ A : Subgroup Gmat, A ≤ (S : Subgroup Gmat) →
      IsElemAbelian 13 A → Nat.card A = 13 ^ 2 →
        GLBCore 13 2 (S : Subgroup Gmat) ⊔ GLBCore 13 1 A = ⊤ := by
  intro S A _ _ _
  rw [c13 S, top_sup_eq]

section D2Rows


theorem d2IndexCaseAt_M_of_gmat_inputs
    (f11 : FusionGenerationOf Gmat 11)
    (c13 : ∀ S : Sylow 13 Gmat, GLBCore 13 2 (S : Subgroup Gmat) = ⊤) :
    CFSG.AGLEmbeddingD2.D2IndexCaseAt (.sporadic .M) fun p => p = 7 ∨ p = 11 ∨ p = 13 :=
  CFSG.AGLEmbeddingD2.d2IndexCaseAt_M_rows_of_Gmat
    CFSG.AGLEmbedding.Norton.MON5_7.three_le_pRank_seven_gmat f11 (sup_thirteen_of_core_two c13)

end D2Rows

end CFSG.AGLEmbedding.Norton.OrdinaryProofs

end
