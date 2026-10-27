module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B5c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Final

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_fact76 (c : Ctx7 G L) (hb : B6Std c) : c.Fact76 := by
  unfold Ctx7.Fact76
  exact ⟨y7b_P7_set_eq c hb, y7b_card_P7 c hb, y7b_P7_cent_t c hb, y7b_P7_le_NM6 c hb⟩

theorem b6Std_of_upto75 {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (h5 : c.toCtx5.Facts5)
    (h : c.Upto75) : B6Std c := by
  unfold Ctx7.Upto75 Ctx7.Upto74 Ctx7.Upto73 Ctx7.Upto72 Ctx7.Upto71 at h
  exact ⟨⟨hH, h5, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩, h.2⟩

theorem y7b_sec76_of (hB : Sec3Inputs) : Sec76 := by
  intro G _ _ L hS hL c h5 h75
  exact y7b_fact76 c (b6Std_of_upto75 (f33hyp_of hB hS hL c.s c.e) h5 h75)

end CFSG.OddStandard.HigherRank.YamadaG23
