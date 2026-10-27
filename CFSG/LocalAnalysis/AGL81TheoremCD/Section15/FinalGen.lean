module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsSmall
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecLiftX1Six
public import Certificates.Certificate5133
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate214003
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB4
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526L2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526L3
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.LiftGen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Row1528Ctx
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526L5
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] [Finite G]

theorem s15_false_gen (hK55 : K55) (hKSML3 : KSML3) (hKOut : KOut) {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hO812 : O812sixAt G M) (hP812 : P812At G M) (hO991 : O991At G M)
    (hO1218 : O1218At G M) (hO98 : O98At G M) (hO89 : O89At G M)
    (ctx : S15CtxGen G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂) : False := by
  have h26 : Row1526W G M T T₁ T₂ := row1526_gen hK55 hKSML3 hKOut ctx h20 h25
  have h27 : Row1527 G M T T₁ T₂ := row1527_gen hKSML3 ctx hLifts h25 h26
  have h28 : Row1528 G M T T₁ T₂ :=
    row1528_gen hK55 hKSML3 hKOut hO812 hP812 hO991 hO1218 hO98 ctx h20 h25 h27
  exact ctx.notLe (rowFinal_gen hKSML3 hO89 ctx hLifts h20 h25 h26 h27 h28)

theorem s15_false_of_rows_gen
    (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (hKSML3 : KSML3) (k21b : K21b) (k21d : K21d) (k420 : K420) (k517_4b : K517_4b)
    (hSix : GNSixAll) (k58 : K58) (k534 : K534) (kA6Z3 : KA6Z3) (k542 : K542)
    (k1525d : K1525d) (hKOut : KOut) (hK55 : K55) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO1211 : O1211At G M) (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    (hO991 : O991At G M) (hO89 : O89At G M) (hO812 : O812sixAt G M) (hP812 : P812At G M)
    (hO1218 : O1218At G M) (hO98 : O98At G M) (ctx : S15CtxGen G M T T₁ T₂)
    (hLifts : RowLifts G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂) (h15 : Row1515 G M T T₁ T₂)
    (h18 : Row1518 G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂) : False := by
  have hR : LiftRankBound G M T T₁ T₂ := liftRankBound_of_gen ctx h11 h18
  have h21 : Row1521 G M T T₁ T₂ :=
    row1521_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k21b k21d k420 ctx hR h15 h20
  have h22 : Row1522 G M T T₁ T₂ :=
    row1522_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k517_4b hSix hO1211 hO1217 hO1521
      ctx hR h11 h15 h20 h21
  have h23 : Row1523 G M T T₁ T₂ := row1523_gen k58 ctx
  have h24 : Row1524 G M T T₁ T₂ := row1524_gen k534 kA6Z3 ctx h22
  have h25 : Row1525 G M T T₁ T₂ :=
    row1525_gen hT hKSML3 hKSMAlt hKSMOdd k542 k1525d hKOut hO1211 hO1217 hO1521
      hO991 hO89 ctx hR hLifts h11 h20 h21 h22 h23 h24
  exact s15_false_gen hK55 hKSML3 hKOut hO812 hP812 hO991 hO1218 hO98 hO89 ctx hLifts h20 h25

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
