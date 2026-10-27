module

public import CFSG.Mathlib.RingTheory.FiniteFixedQuotient

public section

namespace CFSG.LieType.AlgebraicGroups

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

theorem smooth_three_fixed_quotient [Algebra.FiniteType k A] [Algebra.Smooth k A]
    (h3 : (3 : k) ≠ 0) (σ : A ≃ₐ[k] A) (hσ : ∀ a, σ (σ (σ a)) = a) :
    Algebra.Smooth k (A ⧸ Ideal.span (Set.range fun a : A => σ a - a)) := by
  apply CFSG.CommutativeAlgebra.smooth_finite_order_fixed_quotient σ 3 h3
  apply AlgEquiv.ext
  intro a
  simpa only [pow_succ, pow_zero, AlgEquiv.mul_apply, AlgEquiv.one_apply, one_mul] using hσ a

end CFSG.LieType.AlgebraicGroups
