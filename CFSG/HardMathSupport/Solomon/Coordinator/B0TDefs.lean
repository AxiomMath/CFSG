module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def SuzLike (M : Type) [Group M] : Prop :=
  2 ∣ Nat.card M ∧
    ∀ (Q : Sylow 2 M) (α : MulAut M), (∀ x ∈ (Q : Subgroup M), α x = x) →
      ∀ k : ℕ, α ^ 3 ^ k = 1 → α = 1

@[expose] def SuzSections (D : Type) [Group D] : Prop :=
  ∀ (P : Subgroup D) (S : Type) [Group S] [Finite S] [IsSimpleGroup S] (f : P →* S),
    Function.Surjective f → (∃ a b : S, a * b ≠ b * a) → SuzLike S

end CFSG.HardMathSupport.Solomon.Coordinator
