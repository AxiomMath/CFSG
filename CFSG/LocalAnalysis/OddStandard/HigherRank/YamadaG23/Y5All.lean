module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three

theorem sec56_of (hB : Sec3Inputs) : Sec56 :=
  fun G _ _ L hS hL c => y56_fact c (f33hyp_of hB hS hL c.s c.e)

theorem sec5_of_sec3Inputs (hB : Sec3Inputs) : Sec5 :=
  sec5_of_sec3 hB (sec56_of hB)

end CFSG.OddStandard.HigherRank.YamadaG23
