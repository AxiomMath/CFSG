module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def HasOuterTwoElement {K : Type} [Group K] (C I : Subgroup K) : Prop :=
  ∃ c ∈ C, (∃ k : ℕ, c ^ (2 ^ k) = 1) ∧ (∀ x ∈ I, c * x * c⁻¹ ∈ I) ∧
    c ∉ I ⊔ centralizer (I : Set K)

end CFSG.GH74.GLS.SP.Local
