module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abMix2

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup GorensteinWalter Blueprint

namespace KD8ab

@[expose] def CaseA : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (A : L2Data t L) (C : A.CaseKD)
      (S : KDBase A C) (T₁ : Subgroup X) (G : GData S T₁), G.D₁.q0 = .elem →
      G.D₂.q0 = .elem → False

@[expose] def CaseB : Prop :=
  HaradaInput →
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ¬ SectRank4 X → ∀ (t : X) (L : Subgroup X) (A : L2Data t L) (C : A.CaseKD)
      (S : KDBase A C) (T₁ : Subgroup X) (G : GData S T₁), G.D₁.q0 = .homocyclic →
      G.D₂.q0 = .homocyclic → False

theorem fritzKDSection8ab_of_cases (ha : CaseA) (hb : CaseB) : FritzKDSection8ab := by
  intro hH X _ _ _ hX hsr t L A C S T₁ h4 D₁ D₂ h₁ h₂ hne
  rcases (show (D₁.q0 = .elem ∨ D₁.q0 = .homocyclic) ∨ D₁.q0 = .extraspecial by tauto) with
    hq₁ | hq₁ <;>
    rcases (show (D₂.q0 = .elem ∨ D₂.q0 = .homocyclic) ∨ D₂.q0 = .extraspecial by tauto) with
    hq₂ | hq₂
  · by_cases heq : D₁.q0 = D₂.q0
    · obtain ⟨G, hG₁, hG₂⟩ := gdata_of S h4 D₁ D₂ hq₁ hq₂
      rcases hq₁ with h | h
      · exact ha hH X hX hsr t L A C S T₁ G (hG₁ ▸ h) (hG₂ ▸ heq ▸ h)
      · exact hb hH X hX hsr t L A C S T₁ G (hG₁ ▸ h) (hG₂ ▸ heq ▸ h)
    · exact false_of_mixed S h4 D₁ D₂ hq₁ hq₂ heq
  · exact false_of_v₂ S D₁ D₂ hq₂ hq₁
  · exact false_of_v₁ S D₁ D₂ hq₁ hq₂
  · exact hne ⟨hq₁, hq₂⟩

end KD8ab

end CFSG.ComponentClassification.HSFLit
