module

public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge

theorem genFittingFStar_eq_generalizedFitting (G : Type*) [Group G] :
    CFSG.Open.genFittingFStar G = CFSG.generalizedFitting G :=
  CFSG.Adapters.genFittingFStar_eq_foundations G

end CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge
