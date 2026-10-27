module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.IVK

@[expose] def OddOutG2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → LieModel K .G2 0 p f →
    3 < p ^ f → ∀ z : K, orderOf z = 2 → ∀ α : MulAut K, Odd (orderOf α) →
      (∀ x ∈ centralizer ({z} : Set K), α x = x) → α = 1

end CFSG.GH74.GLS.IVK.Proofs2
