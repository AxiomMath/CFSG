module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O89Ctx2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521LB3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PM
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PN
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PO
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PP

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

theorem row1525_gen
    (hT : LieOddRankTable) (hKSML3 : KSML3) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (k542 : K542) (k1525d : K1525d) (kOut : KOut)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G}
    (hO1211 : O1211At G M) (hO1217 : O1217At G M) (hO1521 : O1521At G M)
    (hO991 : O991At G M) (hO89 : O89At G M) {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) (hR : LiftRankBound G M T T₁ T₂)
    (hLifts : RowLifts G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂) (h22 : Row1522 G M T T₁ T₂)
    (h23 : Row1523 G M T T₁ T₂) (h24 : Row1524 G M T T₁ T₂) : Row1525 G M T T₁ T₂ := by
  have h2 : ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls →
        IsLThreeOfExp 1 ↥Ls := by
    intro Ls L hLs hL
    by_contra hnot
    obtain ⟨hLn, hbig⟩ := normal_big_of_not_L3_gen ctx.gn h22 h24 hLs hL hnot
    have hU : ∀ A : Subgroup ↥M, A ≤ L → Nat.card A = 3 → A.map M.subtype ∈ uniqueSet M :=
      fun A hAL hA => mem_uniqueSet_of_order_three_of_ksm_gen hKSMAlt hKSMOdd kOut hO1217 hO991
        ctx hR h11 h20 hLs hL hLn hbig hAL hA
    have hQ : ∀ Ti : Subgroup ↥M, (Ti = T₁ ∨ Ti = T₂) →
        CFSG.Open.pRank 3 (Subgroup.normalizer (Ti : Set ↥M) ⊓ L) ≤ 1 := fun Ti hTi =>
      pRank_normalizer_lift_le_one_gen hT hKSML3 hO1211 hO1217 hO1521 ctx hR h11 h20 h21 hLs hL hTi
        Nat.prime_three (by norm_num)
    rcases hbig with h6 | h8 | h5 | hUU
    · exact false_of_A6_U33_gen k542 ctx hR h11 h20 h23 hLs hL hLn (Or.inl h6) hU
    · exact false_of_A8_L5_gen k1525d hO89 ctx hLs hL hLn (Or.inl h8) hQ hU
    · exact false_of_A8_L5_gen k1525d hO89 ctx hLs hL hLn
        (Or.inr (isL5Two_iff_isLinTwo_five.2 h5)) hQ hU
    · exact false_of_A6_U33_gen k542 ctx hR h11 h20 h23 hLs hL hLn (Or.inr hUU) hU
  exact ⟨sigmaM_eq_seven_of_all_gen ctx hLifts h11 h2, h2⟩

theorem row1525
    (o1211 : O1211) (o1217 : O1217) (o1521 : O1521) (o991 : O991) (o89 : O89)
    (hT : LieOddRankTable) (hKSML3 : KSML3) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (k542 : K542) (k1525d : K1525d) (kOut : KOut)
    {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15Ctx2 G M T T₁ T₂) (hLifts : RowLifts G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h21 : Row1521 G M T T₁ T₂) (h22 : Row1522 G M T T₁ T₂)
    (h23 : Row1523 G M T T₁ T₂) (h24 : Row1524 G M T T₁ T₂) : Row1525 G M T T₁ T₂ :=
  row1525_gen hT hKSML3 hKSMAlt hKSMOdd k542 k1525d kOut
    (O1211At.of_ctx2 o1211 ctx) (O1217At.of_ctx2 o1217 ctx) (O1521At.of_ctx2 o1521 ctx)
    (O991At.of_ctx2 o991 ctx) (O89At.of_ctx2 o89 ctx) (S15CtxGen.of_ctx2 ctx)
    (liftRankBound_of_ctx2 ctx) hLifts h11 h20 h21 h22 h23 h24

end CFSG.LocalAnalysis.RankThreeUC.S15
