module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARem
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open scoped Pointwise
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem false_of_conj_tV (ha : Ctx4P t L S x₁ x₂ lam rho tau)
    (h : ∀ p ∈ ctxPL t tau x₁ x₂, p * t * p⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G)) : False :=
  false_of_conj_in_coset (ctxPL t tau x₁ x₂) (fourGrp x₁ x₂) S t ha.card_P
    (IsPGroup.of_card ha.card_P) (card_fourGrp ha.toCtx4L.toCtx4Q) ha.le_invCent
    ha.relIndex_odd (Ctx4.card_S_seven ha.toCtx4) h

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
