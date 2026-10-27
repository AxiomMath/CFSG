module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTwinCheck

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.PSp4Twin

open CFSG.ComponentClassification.CatFactsSmall.PSp43

@[expose] def tw1 : Equiv.Perm (Fin 45) := x45

@[expose] def tw2 : Equiv.Perm (Fin 45) := tauPerm 0 * tauPerm 15

@[expose] def tws : List (Equiv.Perm (Fin 45)) := [tw2, tw1]

end CFSG.CGT.PushingUpLit.SolKNA.PSp4Twin
