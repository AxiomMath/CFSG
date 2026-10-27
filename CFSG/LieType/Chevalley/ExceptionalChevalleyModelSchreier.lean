module

public import CFSG.LieType.Chevalley.ExceptionalOrdinaryModelSchreier

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem exceptional_Chevalley_model_Schreier
    (G : Type) [Group G] (t : StatedLieTag) (p f : ℕ)
    (ht : t ∈ chevalleyExceptionalTags) (h : ChevalleyExceptionalModel G t p f) :
    Group.IsSolvable (Outer G) ∧
      (t = .G2 ∨ t = .E6 ∨ t = .trialityD4 → derivedSeries (Outer G) 3 = ⊥) ∧
      (t = .F4 ∨ t = .twistedE6 → derivedSeries (Outer G) 5 = ⊥) ∧
      (t = .E7 ∨ t = .E8 → derivedSeries (Outer G) 2 = ⊥) := by
  have hcases : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
      t = .trialityD4 := by
    simpa [chevalleyExceptionalTags] using ht
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hs, h3, -, -⟩ := exceptional_ordinary_model_Schreier G .G2 p f (Or.inl rfl) h
    refine ⟨hs, fun _ => h3 (Or.inl rfl), ?_, ?_⟩ <;>
      rintro (h' | h') <;> exact absurd h' (by decide)
  · obtain ⟨hs, -, h5, -⟩ := exceptional_ordinary_model_Schreier G .F4 p f
      (Or.inr (Or.inl rfl)) h
    refine ⟨hs, ?_, fun _ => h5 rfl, ?_⟩
    · rintro (h' | h' | h') <;> exact absurd h' (by decide)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · obtain ⟨hs, h3, -, -⟩ := exceptional_ordinary_model_Schreier G .E6 p f
      (Or.inr (Or.inr (Or.inl rfl))) h
    refine ⟨hs, fun _ => h3 (Or.inr rfl), ?_, ?_⟩ <;>
      rintro (h' | h') <;> exact absurd h' (by decide)
  · obtain ⟨hs, -, -, h2⟩ := exceptional_ordinary_model_Schreier G .E7 p f
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h
    refine ⟨hs, ?_, ?_, fun _ => h2 (Or.inl rfl)⟩
    · rintro (h' | h' | h') <;> exact absurd h' (by decide)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · obtain ⟨hs, -, -, h2⟩ := exceptional_ordinary_model_Schreier G .E8 p f
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h
    refine ⟨hs, ?_, ?_, fun _ => h2 (Or.inr rfl)⟩
    · rintro (h' | h' | h') <;> exact absurd h' (by decide)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · obtain ⟨h5, -, hs⟩ := exceptional_diagram_fixed_model_Schreier G p f
    have h5' := h5 h
    refine ⟨hs (Or.inl h), ?_, fun _ => h5', ?_⟩
    · rintro (h' | h' | h') <;> exact absurd h' (by decide)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · obtain ⟨-, h3, hs⟩ := exceptional_diagram_fixed_model_Schreier G p f
    have h3' := h3 h
    refine ⟨hs (Or.inr h), fun _ => h3', ?_, ?_⟩ <;>
      rintro (h' | h') <;> exact absurd h' (by decide)

end CFSG.LieType.Chevalley
