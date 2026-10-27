module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Fin
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Fin
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3N
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A3S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem sec72_of (hB : Sec3Inputs) : Sec72 := by
  intro G _ _ L hS hL c hF h71
  exact y7a_fact72 c (f33hyp_of hB hS hL c.s c.e) hF h71

theorem sec73_of (hB : Sec3Inputs) : Sec73 := by
  intro G _ _ L hS hL c hF h72
  exact y7a_fact73 c (f33hyp_of hB hS hL c.s c.e) hF h72.1 h72.2

theorem sec74_of (hB : Sec3Inputs) : Sec74 := by
  intro G _ _ L hS hL c hF h73
  exact y7a_fact74 c (f33hyp_of hB hS hL c.s c.e) hF h73.1.1 h73.2

theorem sec7A_holds (hB : Sec3Inputs) : Sec7A :=
  sec7A_of (sec71_of hB) (sec72_of hB) (sec73_of hB) (sec74_of hB)

end CFSG.OddStandard.HigherRank.YamadaG23
