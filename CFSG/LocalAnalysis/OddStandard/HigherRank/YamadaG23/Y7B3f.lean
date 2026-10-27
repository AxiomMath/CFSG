module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7BAbsF
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B2d
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_R_inf_M6 (c : Ctx7 G L) (hb : B5Std c) : c.s.R ⊓ M6 c.e = c.s.fr.A := by
  refine le_antisymm ?_ ?_
  · calc c.s.R ⊓ M6 c.e ≤ c.s.H ⊓ M6 c.e :=
        inf_le_inf (c.s.R_le_T.trans c.s.sylow_T.1) le_rfl
      _ = c.s.fr.A := hb.h71.2.1.2.1
  · exact le_inf ((s3_A_le_S c.s).trans c.s.S_le_R) (y7b_A_le_M6 c hb)

theorem y7b_R_inf_M7 (c : Ctx7 G L) (hb : B6Std c) : c.s.R ⊓ M7 c.s = c.s.fr.B := by
  refine le_antisymm ?_ ?_
  · calc c.s.R ⊓ M7 c.s ≤ c.s.H ⊓ M7 c.s :=
        inf_le_inf (c.s.R_le_T.trans c.s.sylow_T.1) le_rfl
      _ = c.s.fr.B := hb.h75.1.2.1
  · exact le_inf ((s3_B_le_S c.s).trans c.s.S_le_R) (y7b_B_le_M7 c hb)

theorem y7b_card_R6 (c : Ctx7 G L) (hb : B5Std c) :
    Nat.card ↥(c.s.R ⊔ M6 c.e) = 2 ^ 12 := by
  have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.R) (K := M6 c.e)
    (y7b_R_le_NM6 c hb)
  rw [y7b_R_inf_M6 c hb, y56_card_A hb.hH, y7b_card_R hb.hH, y7b_card_M6 c hb] at h
  norm_num at h ⊢
  omega

theorem y7b_card_R7 (c : Ctx7 G L) (hb : B6Std c) :
    Nat.card ↥(c.s.R ⊔ M7 c.s) = 2 ^ 12 := by
  have h := card_sup_mul_card_inf_of_le_normalizer (H := c.s.R) (K := M7 c.s)
    (y7b_R_le_NM7 hb.hH)
  rw [y7b_R_inf_M7 c hb, y54_card_B hb.hH, y7b_card_R hb.hH, y7b_card_M7 c hb] at h
  norm_num at h ⊢
  omega

theorem y7b_M6_le_NR5 (c : Ctx7 G L) (hb : B6Std c) :
    M6 c.e ≤ normalizer (R5 c.e : Set G) := by
  have hR5 : R5 c.e ≤ c.s.R ⊔ M6 c.e := by
    show c.s.R ⊔ M5 c.e ≤ c.s.R ⊔ M6 c.e
    exact sup_le_sup_left (y7b_M5_le_M6 c hb.toB5Std) _
  have hcard : Nat.card ↥(c.s.R ⊔ M6 c.e) = 2 * Nat.card ↥(R5 c.e) := by
    rw [y7b_card_R6 c hb.toB5Std, y7b_card_R5 c hb]
    norm_num
  have hrel : (R5 c.e).relIndex (c.s.R ⊔ M6 c.e) = 2 :=
    relIndex_eq_of_card_eq_mul hR5 hcard
  exact (le_sup_right : M6 c.e ≤ c.s.R ⊔ M6 c.e).trans
    (le_normalizer_of_relIndex_two hR5 hrel)

theorem y7b_M7_le_NR5 (c : Ctx7 G L) (hb : B6Std c) :
    M7 c.s ≤ normalizer (R5 c.e : Set G) := by
  have hR5 : R5 c.e ≤ c.s.R ⊔ M7 c.s := by
    show c.s.R ⊔ M5 c.e ≤ c.s.R ⊔ M7 c.s
    exact sup_le_sup_left (y7b_M5_le_M7 c hb) _
  have hcard : Nat.card ↥(c.s.R ⊔ M7 c.s) = 2 * Nat.card ↥(R5 c.e) := by
    rw [y7b_card_R7 c hb, y7b_card_R5 c hb]
    norm_num
  have hrel : (R5 c.e).relIndex (c.s.R ⊔ M7 c.s) = 2 :=
    relIndex_eq_of_card_eq_mul hR5 hcard
  exact (le_sup_right : M7 c.s ≤ c.s.R ⊔ M7 c.s).trans
    (le_normalizer_of_relIndex_two hR5 hrel)

theorem y7b_R_le_X76 (c : Ctx7 G L) (hb : B5Std c) : c.s.R ≤ X76 c.e := by
  unfold X76
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · intro x hx
    exact Subgroup.le_normalizer (show x ∈ R5 c.e from Subgroup.mem_sup_left hx)
  · exact y7b_R_le_NM5 c hb
  · exact y7b_R_le_NV1 c hb
  · exact y7b_R_le_NV2 c hb

theorem y7b_M6_le_X76 (c : Ctx7 G L) (hb : B6Std c) : M6 c.e ≤ X76 c.e := by
  unfold X76
  refine le_inf (le_inf (le_inf ?_ ?_) ?_) ?_
  · exact y7b_M6_le_NR5 c hb
  · intro m hm
    exact mem_normalizer_of_forall_conj_mem fun x hx =>
      y7b_M6_norm_M5 c hb.toB5Std m hm x hx
  · intro m hm
    exact mem_normalizer_of_forall_conj_mem fun x hx =>
      y7b_norm_of_V1_le c hb.toB5Std (N := V1 c.e) le_rfl
        ((y7b_V1_le_M5 c hb.toB5Std).trans (y7b_M5_le_M6 c hb.toB5Std)) m hm x hx
  · intro m hm
    exact mem_normalizer_of_forall_conj_mem fun x hx =>
      y7b_M6_norm_V2 c hb.toB5Std m hm x hx

theorem y7b_M7_le_X76 (c : Ctx7 G L) (hb : B6Std c) : M7 c.s ≤ X76 c.e := by
  unfold X76
  exact le_inf (le_inf (le_inf (y7b_M7_le_NR5 c hb) (y7b_M7_le_NM5 c hb))
    (y7b_M7_le_NV1 c hb)) (y7b_M7_le_NV2 c hb)

theorem y7b_R5_le_X76 (c : Ctx7 G L) (hb : B6Std c) : R5 c.e ≤ X76 c.e := by
  show c.s.R ⊔ M5 c.e ≤ X76 c.e
  exact sup_le (y7b_R_le_X76 c hb.toB5Std)
    ((y7b_M5_le_M6 c hb.toB5Std).trans (y7b_M6_le_X76 c hb))

end CFSG.OddStandard.HigherRank.YamadaG23
