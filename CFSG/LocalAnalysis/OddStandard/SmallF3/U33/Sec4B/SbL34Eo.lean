module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34 CFSG.OddStandard.SmallF3.HarrisU33.L34Z

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem sq_mem_V (hl : Ctx4L t L S x₁ x₂ lam rho tau) :
    ∀ a ∈ ctxO t tau x₁ x₂, a * a ∈ fourGrp x₁ x₂ :=
  fun _a ha => O_sq_mem_V hl.toCtx4Q ha

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
