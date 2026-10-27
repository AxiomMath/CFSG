module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12Ctx
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.ToAsc03
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Out13Top

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm6.Glue

theorem stage1M12_of_stage1Data {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (h : Stage1Data G z S Stage12.Kind.m12) : Stage1M12 G z S := by
  cases h with
  | m12 h => exact h

@[expose] def Stage2OddCoreM12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G),
    Stage2Ctx G z Stage12.Kind.m12 S → pPrimeCore 2 ↥(Cen z) = ⊥

theorem s_stage1_thm6_Std_of_stage2
    (hIV3 : ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeaf x Kb)
    (hIV3A7 : ∀ (G : Type) [Group G] [Finite G], Stage12.Std G → pRank 2 G = 3 →
      ∀ (x : G) (Kb : Subgroup (CentralizerBar x)), IV3SylowLeafA7 x Kb)
    (h91 : Sec14.IVK_9_1) (h144 : Lemma14_4) (h145 : Lemma14_5) (hodd : Stage2OddCoreM12) :
    S_stage1_thm6_Std := by
  intro G _ _ hStd h3 hmeets
  obtain ⟨x, T, V, S, a, b, y, o⟩ := s_stage1_out13_Std_of_ext hIV3 hIV3A7 G hStd h3 hmeets
  have hctx := stage2Ctx_m12_of_out13 h91 h144 h145 hStd h3 o
  exact asc03Data_of_stage1M12 hctx.central (stage1M12_of_stage1Data hctx.data) (hodd G _ S hctx)

end CFSG.GH74.GLS.Stage1.Thm6.Prod
