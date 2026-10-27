module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Row1528Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open scoped commutatorElement

section Row28

variable {G : Type} [Group G] [Finite G]

theorem row1528 (hK55 : K55) (hKSML3 : KSML3) (hKOut : KOut) (hO : O812six) (hP : P812)
    (hO991 : O991) (hO1218 : O1218) (hO98 : O98) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    (h25 : Row1525 G M T T₁ T₂) (h27 : Row1527 G M T T₁ T₂) :
    Row1528 G M T T₁ T₂ := by
  exact row1528_gen hK55 hKSML3 hKOut (O812sixAt.of_ctx2 hO ctx) (P812At.of_ctx2 hP ctx)
    (O991At.of_ctx2 hO991 ctx) (O1218At.of_ctx2 hO1218 ctx) (O98At.of_ctx2 hO98 ctx)
    (S15CtxGen.of_ctx2 ctx) h20 h25 h27

end Row28

end CFSG.LocalAnalysis.RankThreeUC.S15
