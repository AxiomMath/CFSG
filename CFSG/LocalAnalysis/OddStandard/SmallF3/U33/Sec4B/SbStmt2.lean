module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

@[expose] def Lemma4_12Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (hc : Ctx11 t L S x₁ x₂ lam rho tau), Lemma4_12Concl t tau x₁ x₂ lam rho

@[expose] def Lemma4_13Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (hG : Sec4Glob G) (hc : Ctx11 t L S x₁ x₂ lam rho tau)
    (h12 : Lemma4_12Concl t tau x₁ x₂ lam rho), Lemma4_13Concl t tau x₁ x₂ rho

@[expose] def Ctx13ExistsStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    (hG : Sec4Glob G) (hc : Ctx11 t L S x₁ x₂ lam rho tau)
    (h12 : Lemma4_12Concl t tau x₁ x₂ lam rho) (h13 : Lemma4_13Concl t tau x₁ x₂ rho),
    ∃ om : G, Ctx13 t L S x₁ x₂ lam rho tau om

end CFSG.OddStandard.SmallF3.HarrisU33
