module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentA

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def Solomon75Lemma54pNorm : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (z : X) (Z : Subgroup X)
    (S : Sylow 2 ↥(normalizer (Z : Set X))), Sec5Data X n z Z S →
    (∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂) →
    ∀ s, IsSec5Inv X Z s → ∀ A, Sec5Comp X n (normalizer (Z : Set X)) A →
      ∀ r ∈ A, r ≠ 1 → r * r = 1 → r * s = s * r →
        ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → r ∈ normalizer (B : Set X)

theorem lemma54p (hF : Solomon75Frac53) (hN : Solomon75NoSwap)
    (hb : Solomon75Lemma54pNorm) : Solomon75Lemma54p := by
  intro X _ _ n z Z S h hk s hs A hA r hrA hr1 hr2 hrs
  exact ⟨sec5_a_prime hF hN h hk hs hA hrA hr1 hr2 hrs, hb X n z Z S h hk s hs A hA r hrA hr1
    hr2 hrs⟩

end CFSG.OddStandard.Solomon75
