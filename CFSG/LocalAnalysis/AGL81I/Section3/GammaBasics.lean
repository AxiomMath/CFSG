module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeNineStatements

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (gammaIn)

variable {G : Type} [Group G] [Finite G]

theorem gammaIn_le (k p : ℕ) (R T : Subgroup G) : gammaIn k p R T ≤ T :=
  Subgroup.map_subtype_le _

end CFSG.LocalAnalysis.AGL81I.Section3
