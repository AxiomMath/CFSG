
module


public import Certificates.Certificate14949

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LieType.Ree CFSG.LieType.SeitzGeneration.ExcHighThree.F4Two

section Links

variable {K : Type} [Field K] [CharP K 2]

end Links

section Closing

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem e6CloseAtTwo_holds : E6CloseAtTwo :=
  Certificates.certificate14949

end Closing

section Glue

end Glue

end CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two
