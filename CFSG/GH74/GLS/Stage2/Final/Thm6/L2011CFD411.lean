module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFId

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

@[expose] def Data411Clauses : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (ε : ℤ) (q : ℕ), (ε = 1 ∨ ε = -1) → Odd q → 3 < q →
    ¬ ((q : ℤ) ≡ ε [ZMOD 8]) → IsLnEps 4 K ε q →
      ∀ z : K, IsCentralInvolution z → ∃ I₁ I₂ : Subgroup K, Data411 z q I₁ I₂

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT
