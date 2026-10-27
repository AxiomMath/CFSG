module

public import CFSG.GH74.GLS.IVK.Defs
public import CFSG.GH74.GLS.IVK.Defs2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GorensteinWalter
  CFSG.GH74.GLS.IVK
open scoped commutatorElement

@[expose] def IsG2Sp4L4U4_fixed (K : Type) [Group K] (q : ℕ) : Prop :=
  (∃ p f : ℕ, p.Prime ∧ q = p ^ f ∧ LieModel K .G2 0 p f) ∨ IsPSp4 K q ∨
    (¬ ((q : ℤ) ≡ 1 [ZMOD 8]) ∧ IsLnEps 4 K 1 q) ∨
    (¬ ((q : ℤ) ≡ -1 [ZMOD 8]) ∧ IsLnEps 4 K (-1) q)

end CFSG.GH74.GLS.IVK.Proofs2
