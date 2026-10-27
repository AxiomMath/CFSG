module

public import CFSG.Holt.NotStar.CasesSupport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega

public section

namespace CFSG.Holt

open MulAction CFSG.Open
open scoped Pointwise

namespace NotStar216

open NotStarCases

section QuaternionKernel

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] [Finite G]

attribute [local instance] CFSG.omega₁_characteristic

end QuaternionKernel

end NotStar216

end CFSG.Holt
