module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Chev

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)

@[expose] def FixedOddFact : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → p ≠ 2 → IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → IsCatalogGroup S → ¬ p ∣ Nat.card S →
    ∀ f : MulAut S, orderOf f = p →
      ∃ y ∈ signalizerFixedSubgroup f, y ≠ 1 ∧ Odd (orderOf y)

@[expose] def FixedTwoFacts : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → p ≠ 2 → IsSimpleGroup S →
    (∃ a b : S, a * b ≠ b * a) → IsCatalogGroup S → ¬ p ∣ Nat.card S → FFChevConclusion S →
    ∀ f : MulAut S, orderOf f = p →
      CFSG.pCore 2 ↥(signalizerFixedSubgroup f) = ⊥ ∧
        ∀ g : MulAut S, IsPGroup 2 (Subgroup.zpowers g) →
          (∀ x ∈ signalizerFixedSubgroup f, g x = x) → g = 1

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
