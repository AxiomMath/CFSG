module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Statements
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def II4_2A7 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsDoubleCoverOfAlt Q 7 →
    (∀ c : Q, c ∉ center Q → ¬ IsFAutomorphism Q (MulAut.conj c)) ∧
    (∀ φ : MulAut Q, IsFAutomorphism Q φ → φ * φ = 1) ∧
    (∀ φ : MulAut Q, φ * φ = 1 → φ ∉ innOf Q → IsKGroupNative Q → IsFAutomorphism Q φ) ∧
    (innOf Q).index = 2 ∧
    (∀ T : Sylow 2 (MulAut Q), Nat.card ↥T = 16 ∧ (¬ ∃ n, IVK.IsDihedralTwoGroup ↥T n) ∧
      ∃ φ ∈ (T : Subgroup (MulAut Q)), φ ∉ innOf Q ∧ φ * φ = 1) ∧
    (∀ c : Q, c ∉ center Q → c * c ∈ center Q →
      ∀ W : Subgroup Q, IsPGroup 2 ↥W → (∀ w ∈ W, c * w = w * c) → IsCyclic ↥W) ∧
    (∀ φ : MulAut Q, IsFAutomorphism Q φ → φ ≠ 1 →
      ∀ P : Subgroup Q, CFSG.GH74.GLS.Stage1.Thm6.IsSylow2In P ⊤ → (∀ p ∈ P, φ p ∈ P) →
        ∃ y ∈ P, orderOf y = 4 ∧ φ y = y)

end CFSG.GH74.GLS.IVK.Lifted
