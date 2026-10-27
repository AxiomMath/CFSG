module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbInputs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

@[expose] def Lemma4_11Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (hG : Sec4Glob G) (hB : Sec4BInputs) (hc : Ctx10 t L S x₁ x₂ lam rho tau),
    Lemma4_11Concl t tau x₁ x₂

@[expose] def Ctx11OfTMStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (hc : Ctx10 t L S x₁ x₂ lam rho tau)
    (h8 : conjIn (ctxM t tau x₁ x₂) t =
      t • (fourGrp x₁ x₂ : Set G) ∪ (t * tau) • (fourGrp x₁ x₂ : Set G)),
    Ctx11 t L S x₁ x₂ lam rho tau

end CFSG.OddStandard.SmallF3.HarrisU33
