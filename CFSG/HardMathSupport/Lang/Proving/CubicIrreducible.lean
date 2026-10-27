module

public import CFSG.HardMathSupport.Lang.Proving.CubeBinomialIrreducible

public section

namespace CFSG.HardMathSupport.Lang.Proving

theorem irreducible_X_pow_three_sub_C {K : Type*} [Field K] {l : K} (hl : ∀ x : K, x ^ 3 ≠ l) :
    Irreducible (Polynomial.X ^ 3 - Polynomial.C l : Polynomial K) :=
  irreducible_X_pow_three_sub_C_of_not_cube l hl

end CFSG.HardMathSupport.Lang.Proving

end
