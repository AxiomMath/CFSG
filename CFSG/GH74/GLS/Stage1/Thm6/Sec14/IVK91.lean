module

public import CFSG.GH74.GLS.Basic
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Prelude

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

@[expose] def IVK_9_1 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (H S : Subgroup Y), IsKGroupNative ↥H → IsSylow2In S H →
    IsElemAb2 S → Nat.card S = 16 →
    ((∀ n ∈ H ⊓ Subgroup.normalizer (S : Set Y), n ∈ Subgroup.centralizer (S : Set Y)) ∨
      ∃ x ∈ H ⊓ Subgroup.normalizer (S : Set Y), ∃ p : ℕ, (p = 3 ∨ p = 5) ∧
        x ^ p ∈ Subgroup.centralizer (S : Set Y) ∧ (∀ s ∈ S, s ≠ 1 → x * s * x⁻¹ ≠ s) ∧
        ∀ n ∈ H ⊓ Subgroup.normalizer (S : Set Y),
          ∃ c ∈ H ⊓ Subgroup.centralizer (S : Set Y), ∃ k : ℕ, n = c * x ^ k) →
    ((pPrimeCoreOf 2 H ⊔ S).subgroupOf H).Normal

end CFSG.GH74.GLS.Stage1.Thm6.Sec14
