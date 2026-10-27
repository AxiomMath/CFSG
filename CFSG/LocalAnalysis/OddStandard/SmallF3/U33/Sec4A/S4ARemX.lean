module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATGX

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem Ctx10.tG_inf_X (hc : Ctx10 t L S x₁ x₂ lam rho tau) :
    {u : G | (∃ g : G, g * t * g⁻¹ = u) ∧ u ∈ ctxX t tau x₁ x₂} =
      conjIn (ctxM t tau x₁ x₂) t :=
  S4A.tG_inf_X_of hc.toCtx hc.l43 hc.l44.1 hc.l48 hc.l49

end CFSG.OddStandard.SmallF3.HarrisU33
