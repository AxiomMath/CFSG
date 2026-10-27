module

public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.Section15Four
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.FinalGen
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.Preamble

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

theorem agl81S15FalseFour_of_rows
    (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (hKSML3 : KSML3) (k21b : K21b) (k21d : K21d) (k420 : K420) (k517_4b : K517_4b)
    (hSix : GNSixAll) (k58 : K58) (k534 : K534) (kA6Z3 : KA6Z3) (k542 : K542)
    (k1525d : K1525d) (hKOut : KOut) (hK55 : K55)
    (h1211 : Section14.TwelveElevenGen) (h1217 : Section15.O1217Gen)
    (h1521 : Section15.O1521Gen) (h1521b : Section15.O1521bGen)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen) (h89 : Section15.O89Gen)
    (h812 : Section15.O812sixGen) (hP812 : Section15.P812Gen) (h98 : Section15.O98Gen)
    (hRows : ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
      ∀ (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M), Section15.S15CtxGen G M T T₁ T₂ →
        RowLifts G M T T₁ T₂ ∧ Row1511 G M T T₁ T₂ ∧ Row1515 G M T T₁ T₂ ∧
          Row1518 G M T T₁ T₂ ∧ Row1520 G M T T₁ T₂) :
    AGL81S15FalseFour := by
  intro G _ _ hS4 hU M T T₁ T₂ ctx
  obtain ⟨hLifts, h11, h15, h18, h20⟩ := hRows G hS4 hU M T T₁ T₂ ctx
  have hO1211 : O1211At G M :=
    O1211At.of_twelveElevenGen h1211 ctx.cstar ctx.maxLocal ctx.p_mem
  have hO1217 : O1217At G M := O1217At.of_gen h1217 ctx
  have hO1521 : O1521At G M := O1521At.of_gen h1521 ctx
  have hO1521b : O1521bAt G M := O1521bAt.of_gen h1521b ctx
  have hO991 : O991At G M := O991At.of_gen h991 ctx
  have hO89 : O89At G M := O89At.of_gen h89 ctx
  have hO812 : O812sixAt G M := O812sixAt.of_gen h812 ctx
  have hP812 : P812At G M := P812At.of_gen hP812 ctx
  have hO98 : O98At G M := O98At.of_gen h98 ctx
  have hO1218 : O1218At G M := O1218At.of_at ctx.cstar ctx.maxLocal hO1211 hO1521b
  exact Section15.s15_false_of_rows_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k21b k21d k420
    k517_4b hSix k58 k534 kA6Z3 k542 k1525d hKOut hK55 hO1211 hO1217 hO1521 hO991
    hO89 hO812 hP812 hO1218 hO98 ctx hLifts h11 h15 h18 h20

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
