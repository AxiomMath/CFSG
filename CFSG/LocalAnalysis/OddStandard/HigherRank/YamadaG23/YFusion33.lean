module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3C1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3C4

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem fact33_of {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : e.Fact33 :=
  ⟨⟨f3_c1 hH, f3_c2 hH, f3_c3 hH⟩, f3_c4 hH, f3_c5 hH, f3_c6 hH, f3_c7 hH, f3_c8 hH, f3_c9 hH,
    f3_c10 hH⟩

theorem fusion33_of (h31 : Fusion31) (hDef : Fusion3Def) (h32 : Fusion32) (hZ : OddCentre)
    (hOut : OutTwo) (hTr : YTransport) : Fusion33 :=
  fun G _ _ L hS hL s e =>
    fact33_of ⟨hS, hZ G L hS hL, hOut _ hL, h31 G L hS hL s, hDef G L hS hL s e,
      h32 G L hS hL s e, hTr G L hS hL s⟩

end CFSG.OddStandard.HigherRank.YamadaG23
