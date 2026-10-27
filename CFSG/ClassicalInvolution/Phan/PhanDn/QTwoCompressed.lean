module

public import CFSG.ClassicalInvolution.Phan.PhanDn.CompGraph

public section

namespace CFSG.ClassicalInvolution.PhanDn

variable {K : Type} [Field K]

theorem compGraph_adj_of_flagGraph {σ : K ≃+* K} {U W : CompVert σ}
    (h : (flagGraph σ 3).Adj U.1 W.1) : (compGraph σ).Adj U W := Or.inl h

theorem FlagVert.finrank_one_two_four {σ : K ≃+* K} (U : FlagVert σ 3) :
    Module.finrank K U.1 = 1 ∨ Module.finrank K U.1 = 2 ∨ Module.finrank K U.1 = 4 := by
  have hle := U.2.1.finrank_le
  have h0 : Module.finrank K U.1 ≠ 0 := fun h => U.2.2.1 (Submodule.finrank_eq_zero.mp h)
  have h3 := U.2.2.2
  omega

theorem CompVert.finrank_one_four {σ : K ≃+* K} (U : CompVert σ) :
    Module.finrank K U.1.1 = 1 ∨ Module.finrank K U.1.1 = 4 := by
  have h := U.1.finrank_one_two_four
  have h2 := U.2
  omega

end CFSG.ClassicalInvolution.PhanDn

end
