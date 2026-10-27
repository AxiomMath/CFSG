module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzYS09Bridge15
public import CFSG.LieType.SeitzGeneration.CubeCoverTwE6Components
public import CFSG.LieType.SeitzGeneration.CubeCoverTwE6NegDatum

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge15

open CFSG.LieType.SeitzGeneration


theorem seitzLowRest19_holds : SeitzLowRest19 :=
  ⟨CubeCoverE6.coverTwE6NegDatum_holds, CubeCoverE6.coverTwE6DiagNotAll24_holds⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzYS09Bridge15

end
