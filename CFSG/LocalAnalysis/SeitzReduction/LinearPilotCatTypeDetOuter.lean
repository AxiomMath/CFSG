module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterHolds

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Outer

theorem catSLmEvenOuterAt_of_three_le {m : ℕ} (hm : 3 ≤ m) : CatSLmEvenOuterAt m :=
  catSLmEvenOuterAt_of_typeDet hm (slmEvenTypeDetAt hm)

end Outer

end CFSG.SeitzReduction.LinearPilot
