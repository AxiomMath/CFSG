module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8ACase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Mixed
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8BCase

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

@[expose] def Fritz812dNotSylowInput : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (S : A7Base X) (F : S.Frame) (T₁ : Subgroup X), S.Sec4 F T₁ →
      ¬ SubConj F.E₁ F.E₂ →
      ∀ (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
        (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)),
      D₁.q0 = .homocyclic → D₂.q0 = .homocyclic → D₁.u = F.xF * F.yF → D₂.u = S.z * F.yF →
      ∀ Q : Subgroup X, IsPGroup 2 Q → D₁.S₁ ≤ Q → Q = D₁.S₁

theorem fritzA7Section8_of_input (h : Fritz812dNotSylowInput) : FritzA7Section8 := by
  intro hH X _ _ _ hX hsr S F T₁ h4 hnc D₁ D₂ hq₁ hq₂
  rcases split h4 D₁ D₂ hq₁ hq₂ with ⟨hq₁', hq₂', -, -, hu₁, hu₂⟩ | ⟨hq₁', hq₂', hu₁, hu₂⟩
  · by_cases hne : D₁.q0 = D₂.q0
    · rcases hq₁' with h₁ | h₁
      · exact (AData.mk h4 D₁ D₂ h₁ (hne ▸ h₁) hu₁ hu₂).false_of hX hnc
      · exact (BData.mk h4 D₁ D₂ h₁ (hne ▸ h₁) hu₁ hu₂).false_of_maximal hX
          (h hH X hX hsr S F T₁ h4 hnc D₁ D₂ h₁ (hne ▸ h₁) hu₁ hu₂)
    · exact (GData.mk h4 D₁ D₂ hq₁' hq₂' hu₁ hu₂).false_of_ne hne
  · exact (CData.mk h4 D₁ D₂ hq₁' hq₂' hu₁ hu₂).false_of hX hnc

end Sec8

end CFSG.ComponentClassification.HSFLit
