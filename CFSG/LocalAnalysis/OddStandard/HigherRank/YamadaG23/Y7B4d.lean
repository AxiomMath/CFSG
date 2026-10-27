module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B3e

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_C2_le_R5 (c : Ctx7 G L) (hb : B5Std c) : c.s.C₂ ≤ R5 c.e := by
  rw [y54_C2_eq_M2t c.toCtx5 hb.hH, hb.h72.1.1]
  change c.s.fr.B ⊔ V2 c.e ⊔ zpowers c.s.t ≤ c.s.R ⊔ M5 c.e
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (s3_B_le_S c.s).trans (c.s.S_le_R.trans le_sup_left)
  · exact (show V2 c.e ≤ M3 c.s from inf_le_left).trans
      ((show M3 c.s ≤ M5 c.e from le_sup_left).trans le_sup_right)
  · exact le_trans (Subgroup.zpowers_le.mpr (s3_t_mem_R c.s)) le_sup_left

theorem y7b_comm_mem_EFV2 (c : Ctx7 G L) (hb : B5Std c) {x : G} (hx : ⁅x, c.s.t⁆ ∈ M5 c.e) :
    ⁅x, c.s.t⁆ ∈ EFV2 c.e := by
  have ht2 : c.s.t * c.s.t = 1 := by
    have h := pow_orderOf_eq_one c.s.t
    rw [c.s.t_order, pow_two] at h
    exact h
  have ht_inv : c.s.t⁻¹ = c.s.t := inv_eq_of_mul_eq_one_right ht2
  set m : G := ⁅x, c.s.t⁆ with hm
  have hmM5 : m ∈ M5 c.e := by rw [hm]; exact hx
  have hm_eq : m = x * c.s.t * x⁻¹ * c.s.t := by
    rw [hm, commutatorElement_def, ht_inv]
  have hmt : m * c.s.t = x * c.s.t * x⁻¹ := by
    rw [hm_eq, mul_assoc, ht2, mul_one]
  have hu : (x * c.s.t * x⁻¹) * (x * c.s.t * x⁻¹) = 1 := by
    have h : x * c.s.t * x⁻¹ * (x * c.s.t * x⁻¹) = x * (c.s.t * c.s.t) * x⁻¹ := by
      group
    rw [h, ht2]; group
  have hconj : (m * c.s.t) * (m * c.s.t) = 1 := by
    rw [hmt]; exact hu
  have htmt : c.s.t * m * c.s.t = m⁻¹ := by
    have h : m * (c.s.t * m * c.s.t) = m * m⁻¹ := by
      rw [mul_inv_cancel]
      simpa only [mul_assoc] using hconj
    exact mul_left_cancel h
  have hV2 : ⁅c.s.t, m⁆ ∈ V2 c.e := by
    have hcomm : ⁅c.s.t, m⁆ = (m ^ 2)⁻¹ := by
      rw [commutatorElement_def, ht_inv, htmt, pow_two, mul_inv_rev]
    rw [hcomm]
    exact y7b_V1_le_V2 c hb ((V1 c.e).inv_mem ((y7b_M5_comm_sq c hb).2 m hmM5))
  exact y7b_mem_EFV2 c hb m hmM5 hV2

theorem y7b_exists_adjust (c : Ctx7 G L) (hb : B5Std c) {x : G} (hx : ⁅x, c.s.t⁆ ∈ M5 c.e) :
    ∃ m ∈ M5 c.e, ⁅m * x, c.s.t⁆ ∈ V2 c.e := by
  have hm0 : ⁅x, c.s.t⁆ ∈ EFV2 c.e := y7b_comm_mem_EFV2 c hb hx
  have hy : (⁅x, c.s.t⁆)⁻¹ ∈ EFV2 c.e := (EFV2 c.e).inv_mem hm0
  obtain ⟨m, hmM5, hmV2⟩ := y7b_EFV2_onto c hb (⁅x, c.s.t⁆)⁻¹ hy
  refine ⟨m, hmM5, ?_⟩
  have hm0mt : ⁅x, c.s.t⁆ * ⁅m, c.s.t⁆ ∈ V2 c.e := by
    simpa using hmV2
  have hV1 : ⁅m, ⁅x, c.s.t⁆⁆ ∈ V2 c.e :=
    y7b_V1_le_V2 c hb ((y7b_M5_comm_sq c hb).1 m hmM5 ⁅x, c.s.t⁆ hx)
  have hcomp : ⁅m * x, c.s.t⁆ = ⁅m, ⁅x, c.s.t⁆⁆ * ⁅x, c.s.t⁆ * ⁅m, c.s.t⁆ := by
    simp only [commutatorElement_def]; group
  rw [hcomp, mul_assoc]
  exact (V2 c.e).mul_mem hV1 hm0mt

end CFSG.OddStandard.HigherRank.YamadaG23
