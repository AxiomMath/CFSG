module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

variable {G : Type} [Group G]

structure Sig4 (t tau x₁ x₂ : G) where
  φ : ↥(ctxLO t tau x₁ x₂) →* Equiv.Perm (Fin 4)
  surj : Function.Surjective φ
  ker_eq : φ.ker = (ctxO t tau x₁ x₂).subgroupOf (ctxLO t tau x₁ x₂)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
