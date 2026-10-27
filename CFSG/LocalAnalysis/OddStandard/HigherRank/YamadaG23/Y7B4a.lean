module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3a

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_M5_le_AM5 (c : Ctx7 G L) : M5 c.e ≤ AM5 c.e := by
  unfold AM5
  exact le_sup_right

theorem y7b_M5_le_BM5 (c : Ctx7 G L) : M5 c.e ≤ BM5 c.e := by
  unfold BM5
  exact le_sup_right

theorem y7b_AM5_le_SM5 (c : Ctx7 G L) : AM5 c.e ≤ SM5 c.e := by
  unfold AM5 SM5
  exact sup_le_sup_right (s3_A_le_S c.s) _

theorem y7b_BM5_le_SM5 (c : Ctx7 G L) (hb : B5Std c) : BM5 c.e ≤ SM5 c.e := by
  unfold BM5 SM5
  exact sup_le_sup_right (s3_B_le_S c.s) _

theorem y7b_SM5_le_R5 (c : Ctx7 G L) : SM5 c.e ≤ R5 c.e := by
  unfold SM5 R5
  exact sup_le_sup_right c.s.S_le_R _

theorem y7b_AM5_le_M6 (c : Ctx7 G L) (hb : B5Std c) : AM5 c.e ≤ M6 c.e := by
  unfold AM5
  exact sup_le (y7b_A_le_M6 c hb) (y7b_M5_le_M6 c hb)

theorem y7b_BM5_le_M7 (c : Ctx7 G L) (hb : B6Std c) : BM5 c.e ≤ M7 c.s := by
  unfold BM5
  exact sup_le (y7b_B_le_M7 c hb) (y7b_M5_le_M7 c hb)

theorem y7b_relIndex_M5_AM5 (c : Ctx7 G L) (hb : B6Std c) :
    (M5 c.e).relIndex (AM5 c.e) = 2 := by
  refine relIndex_eq_of_card_eq_mul (y7b_M5_le_AM5 c) ?_
  rw [y7b_card_AM5 c hb, y7b_card_M5 c hb.toB5Std]
  norm_num

theorem y7b_relIndex_M5_BM5 (c : Ctx7 G L) (hb : B6Std c) :
    (M5 c.e).relIndex (BM5 c.e) = 2 := by
  refine relIndex_eq_of_card_eq_mul (y7b_M5_le_BM5 c) ?_
  rw [y7b_card_BM5 c hb, y7b_card_M5 c hb.toB5Std]
  norm_num

theorem y7b_relIndex_AM5_SM5 (c : Ctx7 G L) (hb : B6Std c) :
    (AM5 c.e).relIndex (SM5 c.e) = 2 := by
  refine relIndex_eq_of_card_eq_mul (y7b_AM5_le_SM5 c) ?_
  rw [y7b_card_SM5 c hb, y7b_card_AM5 c hb]
  norm_num

theorem y7b_relIndex_BM5_SM5 (c : Ctx7 G L) (hb : B6Std c) :
    (BM5 c.e).relIndex (SM5 c.e) = 2 := by
  refine relIndex_eq_of_card_eq_mul (y7b_BM5_le_SM5 c hb.toB5Std) ?_
  rw [y7b_card_SM5 c hb, y7b_card_BM5 c hb]
  norm_num

theorem y7b_relIndex_SM5_R5 (c : Ctx7 G L) (hb : B6Std c) :
    (SM5 c.e).relIndex (R5 c.e) = 2 := by
  refine relIndex_eq_of_card_eq_mul (y7b_SM5_le_R5 c) ?_
  rw [y7b_card_R5 c hb, y7b_card_SM5 c hb]
  norm_num

theorem y7b_relIndex_AM5_M6 (c : Ctx7 G L) (hb : B6Std c) :
    (AM5 c.e).relIndex (M6 c.e) = 2 := by
  refine relIndex_eq_of_card_eq_mul (y7b_AM5_le_M6 c hb.toB5Std) ?_
  rw [y7b_card_M6 c hb.toB5Std, y7b_card_AM5 c hb]
  norm_num

theorem y7b_relIndex_BM5_M7 (c : Ctx7 G L) (hb : B6Std c) :
    (BM5 c.e).relIndex (M7 c.s) = 2 := by
  refine relIndex_eq_of_card_eq_mul (y7b_BM5_le_M7 c hb) ?_
  rw [y7b_card_M7 c hb, y7b_card_BM5 c hb]
  norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
