module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldLinear

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {n : ℕ}

theorem exists_conjAut_fieldAut_of_pow_three [Finite K] (hn : 3 ≤ n)
    (β : MulAut (projectiveSL n K)) (hβ : β ^ 3 = 1) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), β = conjAut n K A * fieldAut n K σ :=
  mem_semilinearAutGroup_iff.mp
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.mem_semilinearAutGroup_of_pow hn
      (by decide : Odd 3) hβ)

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
