module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.TwoSignalizer

public section

namespace CFSG.GH72

theorem theorem_2_1 {G : Type} [Group G] [Finite G] (A : Subgroup G)
    (hA : CFSG.Open.IsElemAbelian 2 A) (hrank : 16 ≤ Nat.card A) (θ : G → Subgroup G)
    (hcent : ∀ a ∈ A, a ≠ 1 → θ a ≤ Subgroup.centralizer {a})
    (hodd : ∀ a ∈ A, a ≠ 1 → Odd (Nat.card (θ a)))
    (hinv : ∀ a ∈ A, a ≠ 1 → A ≤ Subgroup.normalizer (θ a : Set G))
    (hbal : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → θ a ⊓ Subgroup.centralizer {b} ≤ θ b) :
    Odd (Nat.card (⨆ (a : G) (_ : a ∈ A) (_ : a ≠ 1), θ a : Subgroup G)) :=
  (CFSG.SignalizerFunctorTheorem.two_signalizer_completion A hA (by omega) θ hcent hodd hinv
    hbal).1

end CFSG.GH72
