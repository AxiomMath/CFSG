module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFSA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFSB

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem fusion32_of (h31 : Fusion31) (hZ : OddCentre) (hOut : OutTwo) : Fusion32 :=
  fun G _ _ L hS hL s e => by
    have hZ' : Odd (Nat.card ↥(center ↥L)) := hZ G L hS hL
    have hA : LFactsA s := lfactsA_of_setting hS hZ' s
    have h31' : s.Fact31 := h31 G L hS hL s
    by_cases hRT : s.R = s.T
    · exact fusion32_of_RT s hS hZ' h31' hA e hRT
    · exact fusion32_of_RneT s hS hZ' (hOut _ hL) h31' hA e hRT

end CFSG.OddStandard.HigherRank.YamadaG23
