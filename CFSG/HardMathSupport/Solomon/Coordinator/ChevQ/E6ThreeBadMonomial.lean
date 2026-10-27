module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoCases
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadNormalizes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three


theorem e6BadCube_of_monomial : E6ThreeNotAll24NFB2 :=
  e6BadCube_of_monomial_of
    (fun _ _ _ hK3 _ h3 h1 b hb0 hb2 => e6BadParabolic_normalizes hK3 h3 h1 b hb0 hb2)
    (fun _ _ _ _ a _ hβ hν => bm_normalizes_rootSubgroup a hβ hν)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
