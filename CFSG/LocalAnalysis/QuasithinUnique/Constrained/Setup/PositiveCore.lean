module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Interfaces

public section

namespace CFSG.QuasithinUnique

theorem positiveTwoCoreSQTK : PositiveTwoCoreSQTK :=
  fun _ _ _ _ _ hset P hP => hset.qtke.1 P hP

end CFSG.QuasithinUnique
