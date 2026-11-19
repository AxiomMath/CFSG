module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

@[expose] def Lemma4_17Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} (_hG : Sec4Glob G)
    (_hc : Ctx13 t L S x₁ x₂ lam rho tau om) {𝒮 : Subgroup G}
    (_h𝒮 : IsSylowIn 2 𝒮 (ctxK t tau x₁ x₂ rho)) (_hU : ctxU t tau x₁ x₂ lam ≤ 𝒮)
    (_hK : ctxQ t tau x₁ x₂ rho <
      ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G)),
    Lemma4_17Concl t tau x₁ x₂ rho om 𝒮

@[expose] def Lemma4_18Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} (_hG : Sec4Glob G)
    (_hc : Ctx13 t L S x₁ x₂ lam rho tau om) {𝒮 : Subgroup G}
    (_h𝒮 : IsSylowIn 2 𝒮 (ctxK t tau x₁ x₂ rho)) (_hU : ctxU t tau x₁ x₂ lam ≤ 𝒮)
    (_hK : ctxK t tau x₁ x₂ rho ⊓ centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) =
      ctxQ t tau x₁ x₂ rho),
    Lemma4_18Concl t tau x₁ x₂ lam rho om 𝒮

end CFSG.OddStandard.SmallF3.HarrisU33
