module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42ThreeA7Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42DichProof

public section

namespace CFSG.QuasithinUnique.Bridge

theorem threeA7Exclusion : ThreeA7Exclusion :=
  fun W _ _ hW L E hq hirr he hZ hEN hE hel hquad =>
    ThreeA7Excl.threeA7_core W hW L E hq hirr he hZ hEN hE hel hquad

end CFSG.QuasithinUnique.Bridge
