module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YBundle
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y55
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem f33hyp_of (hB : Sec3Inputs) (hS : HRSetting G L) (hL : HRG23 (L ⧸ center L))
    (s : Setting3 G L) (e : Setting3.Ext s) : F33Hyp s e :=
  ⟨hS, hB.oddCentre G L hS hL, hB.outTwo _ hL, hB.f31 G L hS hL s, hB.fDef G L hS hL s e,
    hB.f32 G L hS hL s e, hB.transport G L hS hL s⟩

theorem sec52_of (hB : Sec3Inputs) : Sec52 :=
  fun G _ _ L hS hL c => y52_fact (f33hyp_of hB hS hL c.s c.e)

theorem sec53_of (hB : Sec3Inputs) : Sec53 :=
  fun G _ _ L hS hL c => y53_fact (f33hyp_of hB hS hL c.s c.e)

theorem sec54_of (hB : Sec3Inputs) : Sec54 :=
  fun G _ _ L hS hL c => y54_fact c (f33hyp_of hB hS hL c.s c.e)

theorem sec55_of (hB : Sec3Inputs) : Sec55 :=
  fun G _ _ L hS hL c => y55_fact c (f33hyp_of hB hS hL c.s c.e)

theorem sec57_of (hB : Sec3Inputs) : Sec57 :=
  fun G _ _ L hS hL c => y57_fact c (f33hyp_of hB hS hL c.s c.e)

theorem sec5_of_sec3 (hB : Sec3Inputs) (h56 : Sec56) : Sec5 :=
  sec5_of (sec52_of hB) (sec53_of hB) (sec54_of hB) (sec55_of hB) h56 (sec57_of hB)

end CFSG.OddStandard.HigherRank.YamadaG23
