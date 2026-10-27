module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7w
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B8g

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_fact75_holds (c : Ctx7 G L) (hb : B5Std c) : c.Fact75 :=
  y7b_fact75 c hb (fun hRT => y7b_M4_le_M7_of_ne c hb hRT)

theorem y7b_sec75_holds (hB : Sec3Inputs) : Sec75 := by
  intro G _ _ L hS hL c h5 h4
  have hb : B5Std c := y7b_b5Std_of_upto74 (f33hyp_of hB hS hL c.s c.e) h5 h4
  exact y7b_fact75_holds c hb

theorem sec7B_holds (hB : Sec3Inputs) : Sec7B :=
  sec7B_of (y7b_sec75_holds hB) (y7b_sec76_of hB)

end CFSG.OddStandard.HigherRank.YamadaG23
