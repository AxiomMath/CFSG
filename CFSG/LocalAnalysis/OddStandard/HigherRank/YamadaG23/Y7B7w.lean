module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7t
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7u
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7v

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_M4_le_M7 (c : Ctx7 G L) (hb : B5Std c)
    (hM4 : c.s.R ≠ c.s.T → M4 c.e ≤ M7 c.s) : M4 c.e ≤ M7 c.s := by
  by_cases hRT : c.s.R = c.s.T
  · exact y7b_M4_le_M7_of_R_eq_T c hb hRT
  · exact hM4 hRT

theorem y7b_fact75 (c : Ctx7 G L) (hb : B5Std c)
    (hM4 : c.s.R ≠ c.s.T → M4 c.e ≤ M7 c.s) : c.Fact75 := by
  unfold Ctx7.Fact75
  exact ⟨⟨y7b_X_eq_NM7 c hb, y7b_H_inf_M7 c hb, y7b_actsTrans c hb, y7b_quotModIso c hb⟩,
    ⟨y7b_C7_eq_M7_t c hb, y7b_M4_le_M7 c hb hM4, y7b_V2_le_cen_M7 c hb⟩,
    y7b_M7_secProp c hb, y7b_g_comm_M7 c hb⟩

theorem y7b_b5Std_of_upto74 {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (h5 : c.toCtx5.Facts5)
    (h : c.Upto74) : B5Std c := by
  unfold Ctx7.Upto74 Ctx7.Upto73 Ctx7.Upto72 Ctx7.Upto71 at h
  exact ⟨hH, h5, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
