module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.Omega
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Holt

open MulAction

namespace IsNaturalPSL2

variable {Δ : Type*} {L : Subgroup (Equiv.Perm Δ)} {n : ℕ}

section Quotient

attribute [local instance] omega₁_characteristic

end Quotient

end IsNaturalPSL2

end CFSG.Holt
