module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

@[expose] def TableVIIFiveAInv : Prop :=
  ∀ (H : Type) [Group H] (E : Subgroup H), TwoHS.IsF5Centralizer H E →
    ∀ a z b z₁ : H, TwoHSFacts H a z b z₁ → A8Dict z b →
      ∀ y : H, IsConj (a * z) y → ∀ c ∈ tab6Set a z b z₁ y 5, ∃ s ∈ Gx y ⊓ Gx c, IsConj b s

theorem tableVII_fiveAInv_of_suborbit (hS : SuborbitFacts) : TableVIIFiveAInv :=
  hS.tableVI_5A_b

end CFSG.EvenSporadicStandard.HNRecog.Section3
