module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def L34SigmaFourInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
    {W : Subgroup G} {v : G},
    Sec4Glob G → Sec4BInputs → Ctx4A t L S x₁ x₂ lam rho tau → Ctx4V t x₁ x₂ lam tau W v →
      ∃ φ : ↥(ctxLO t tau x₁ x₂) →* Equiv.Perm (Fin 4),
        Function.Surjective φ ∧ φ.ker = (ctxO t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)

end CFSG.OddStandard.SmallF3.HarrisU33
