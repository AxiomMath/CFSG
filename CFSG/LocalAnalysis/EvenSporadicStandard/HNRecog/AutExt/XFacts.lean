module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XAutDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

@[expose] def XInnerFacts : Prop :=
  ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
      ∀ x : H, IsConj z x → ∀ A : ↥(Gx x), (A : H) = a → XAutInner ↥(Gx x) A

@[expose] def XCentFacts : Prop :=
  ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
      ∀ x : H, IsConj z x → ∀ T : ↥(Gx x), T * T = 1 →
        (Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(Gx x))) = 768 ∨
          Nat.card ↥(Subgroup.centralizer ({T} : Set ↥(Gx x))) = 384) →
        XAutCent ↥(Gx x) T

end CFSG.EvenSporadicStandard.HNRecog.Section4
