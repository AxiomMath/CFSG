module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Primed
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4Fin
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Fin

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three

theorem sec61'_of (hB : Sec3Inputs) : Sec61' :=
  fun _ _ _ _ hS hL c hF => y6_fact61 c (f33hyp_of hB hS hL c.s c.e) hF

theorem sec62'_of (hB : Sec3Inputs) (h1 : Sec2.Lemma26Pres2) (h2 : Sec2.Lemma26HS)
    (h3 : Sec2.Lemma27G23) : Sec62' :=
  fun _ _ _ _ hS hL c hF => y6_fact62 c (f33hyp_of hB hS hL c.s c.e) hF h1 h2 h3 hL

theorem sec63'_of (hB : Sec3Inputs) (hHS : HSSylowFacts) : Sec63' :=
  fun _ _ _ _ hS hL c hF h61 h62 =>
    y63_fact63 hHS c hS (f33hyp_of hB hS hL c.s c.e) hF h61 h62

theorem sec64a'_of (hB : Sec3Inputs) : Sec64a' :=
  fun _ _ _ _ hS hL c hF h6 => y6_four123 c (f33hyp_of hB hS hL c.s c.e) hF h6.2.2

theorem sec64b'_of (hB : Sec3Inputs) (hY : Y6Four4a) : Sec64b' :=
  fun G _ _ L hS hL c hF h6 =>
    y6b_four4 c (f33hyp_of hB hS hL c.s c.e) hF h6.2.2 h6.1 (hY G L hS hL c hF h6)

end CFSG.OddStandard.HigherRank.YamadaG23
