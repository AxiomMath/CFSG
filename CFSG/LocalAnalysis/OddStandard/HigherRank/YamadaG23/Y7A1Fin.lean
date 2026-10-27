module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1M3C
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1C4C
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModD

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_fact71 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) : c.Fact71 := by
  obtain ⟨ψ, lab, P, hP⟩ := y7a_reg_data c hH hF
  refine ⟨y7a_fact71_1 c hH, ⟨y7a_NC1_eq_NHA_M6 c hH hF hP, y7a_H_inf_M6 c hH hF hP,
    y7a_acts_trans c hH hF hP, y7a_comm_M6_AV c hH hF, y7a_quotModIso c hH hF hP⟩,
    (y7a_C6_eq_M6 c hH hF).2, ?_, ?_⟩
  · intro m hm
    refine Subgroup.mem_inf.mpr ⟨y7a_M3_le_C6 c hH hF hm, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val
      ((y7a_M3_elemAbelian c hH).1.is_comm.comm ⟨v, y7a_V1_le_M3 c hv⟩ ⟨m, hm⟩)
  · intro m hm
    exact Subgroup.mem_inf.mpr ⟨y7a_C4_le_C6 c hH hF (Subgroup.mem_inf.mp hm).1,
      (Subgroup.mem_inf.mp hm).2⟩

theorem sec71_of (hB : Sec3Inputs) : Sec71 := by
  intro G _ _ L hS hL c hF
  exact y7a_fact71 c (f33hyp_of hB hS hL c.s c.e) hF

end CFSG.OddStandard.HigherRank.YamadaG23
