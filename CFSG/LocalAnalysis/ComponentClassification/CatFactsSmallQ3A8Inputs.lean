module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck

public section

namespace CFSG.ComponentClassification.CatFactsSmall.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

local notation "P8" => Equiv.Perm (Fin 8)

@[expose] def oddTest (x : P8) : Bool := decide (x ^ 15 = 1) || decide (x ^ 7 = 1)

end CFSG.ComponentClassification.CatFactsSmall.A8
