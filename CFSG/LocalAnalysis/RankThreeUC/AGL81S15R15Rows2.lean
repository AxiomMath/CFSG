module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Six
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KA6Z3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB3
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem s15_rows_21_to_24
    (hT : LieOddRankTable) (hK517_4b : K517_4b) (hK21d : K21d) (hK58 : K58) (hK534 : K534)
    (hSix : GNSixAll)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) (hKSMOdd : KSMOdd) (hKSMAlt : KSMAlt) (hK21b : K21b)
    (hK420 : K420)
    (hO1211 : O1211) (hO1217 : O1217) (hO1521 : O1521)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂) (h15 : Row1515 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂) :
    Row1521 G M T T₁ T₂ ∧ Row1522 G M T T₁ T₂ ∧ Row1523 G M T T₁ T₂ ∧
      Row1524 G M T T₁ T₂ := by
  have h21 : Row1521 G M T T₁ T₂ :=
    row1521 hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hK21b hK21d hK420 ctx h15 h20
  have h22 : Row1522 G M T T₁ T₂ :=
    row1522 hO1211 hO1217 hO1521 hT hKSMAlt hKSMOdd hKSMU4 hKSML3 hK517_4b hSix ctx h11 h15
      h20 h21
  have h23 : Row1523 G M T T₁ T₂ := row1523 hK58 ctx
  have h24 : Row1524 G M T T₁ T₂ := row1524 hK534 KA6Z3_holds ctx h22
  exact ⟨h21, h22, h23, h24⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
