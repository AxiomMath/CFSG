module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


@[expose] def Lemma4_3Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (hI : Sec4Inputs) (hG : Sec4Glob G) (hc : Ctx t L S x₁ x₂ lam rho tau)
    (h2 : Lemma4_2Concl S), Lemma4_3Concl t

theorem ctx4_of_ctx (h43 : Lemma4_3Stmt) (hI : Sec4Inputs) (hG : Sec4Glob G)
    (hc : Ctx t L S x₁ x₂ lam rho tau) : Ctx4 t L S x₁ x₂ lam rho tau :=
  have h2 := lemma4_2 hG hc
  have h3 := h43 hI hG hc h2
  { toCtx := hc, l42 := h2, l43 := h3, l44 := lemma4_4 hc h2 h3 }

end CFSG.OddStandard.SmallF3.HarrisU33
