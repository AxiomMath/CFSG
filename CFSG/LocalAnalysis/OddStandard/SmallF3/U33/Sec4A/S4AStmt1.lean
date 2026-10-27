module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}


@[expose] def Lemma4_1Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (hI : Sec4Inputs) (hG : Sec4Glob G) (h0 : Ctx0 t L S x₁ x₂ lam rho), Lemma4_1Concl t L

@[expose] def CtxOfLemma4_1Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h0 : Ctx0 t L S x₁ x₂ lam rho) (h1 : Lemma4_1Concl t L),
    ∃ tau : G, Ctx t L S x₁ x₂ lam rho tau

theorem exists_ctx (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt) (hI : Sec4Inputs)
    (hG : Sec4Glob G) (h0 : Ctx0 t L S x₁ x₂ lam rho) :
    ∃ tau : G, Ctx t L S x₁ x₂ lam rho tau :=
  h41c h0 (h41 hI hG h0)

end CFSG.OddStandard.SmallF3.HarrisU33
