module

public import CFSG.CGT.Timmesfeld75.Config

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

@[expose] def InvolutionClassInput : Prop :=
  ∀ (K : Type) [Group K],
    ((∃ f : ℕ, 2 ≤ f ∧ Nonempty (K ≃* PSL(2, GaloisField 2 f))) ∨
      (∃ a : ℕ, 1 ≤ a ∧ Nonempty (K ≃* Sz a)) ∨
      (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (K ≃* DihedralGroup n))) →
    ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y

variable {G : Type*} [Group G]

structure Sec3 (T T₁ : Subgroup G) : Prop where
  cfg : Cfg T T₁
  conj : ∃ x ∈ T ⊔ T₁, T₁ = conjSubgroup x T
  invol : ∀ a ∈ T ⊔ T₁, a * a = 1 → a ∉ cfgM T T₁ → ∃ x ∈ T ⊔ T₁, a ∈ conjSubgroup x T
  trans : ∀ x ∈ T ⊔ T₁, conjSubgroup x T ≠ T → normIn (conjSubgroup x T) T ≤ cfgM T T₁

end CFSG.CGT.Timmesfeld75
