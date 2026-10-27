module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Facts

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G]

@[expose] def kComponent (L : Subgroup G) (u : L) : Subgroup G :=
  (derivedCentralizer u).map L.subtype

end CFSG.EvenSporadicStandard.RuStd
