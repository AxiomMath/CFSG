module

public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem exceptional_ordinary_model_Schreier
    (G : Type) [Group G] (t : StatedLieTag) (p f : ℕ)
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (h : ChevalleyExceptionalModel G t p f) :
    Group.IsSolvable (Outer G) ∧
      (t = .G2 ∨ t = .E6 → derivedSeries (Outer G) 3 = ⊥) ∧
      (t = .F4 → derivedSeries (Outer G) 5 = ⊥) ∧
      (t = .E7 ∨ t = .E8 → derivedSeries (Outer G) 2 = ⊥) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨h3, -, hs⟩ := exceptional_G2_F4_model_Schreier G .G2 p f (Or.inl rfl) h
    refine ⟨hs, fun _ => h3 rfl, fun h' => absurd h' (by decide), ?_⟩
    rintro (h' | h') <;> exact absurd h' (by decide)
  · obtain ⟨-, h5, hs⟩ := exceptional_G2_F4_model_Schreier G .F4 p f (Or.inr rfl) h
    refine ⟨hs, ?_, fun _ => h5 rfl, ?_⟩
    · rintro (h' | h') <;> exact absurd h' (by decide)
    · rintro (h' | h') <;> exact absurd h' (by decide)
  · have hm : UntwistedChevalleyModel G .E6 (p ^ f) := h.2
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
    have h3 : derivedSeries (Outer G) 3 = ⊥ :=
      derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).1
    refine ⟨⟨⟨3, h3⟩⟩, fun _ => h3, fun h' => absurd h' (by decide), ?_⟩
    rintro (h' | h') <;> exact absurd h' (by decide)
  · have hm : UntwistedChevalleyModel G .E7 (p ^ f) := h.2
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hm
    have h2 : derivedSeries (Outer G) 2 = ⊥ :=
      derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).2.1
    refine ⟨⟨⟨2, h2⟩⟩, ?_, fun h' => absurd h' (by decide), fun _ => h2⟩
    rintro (h' | h') <;> exact absurd h' (by decide)
  · have hm : UntwistedChevalleyModel G .E8 (p ^ f) := h.2
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 hm
    have h2 : derivedSeries (Outer G) 2 = ⊥ :=
      derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).2.2
    refine ⟨⟨⟨2, h2⟩⟩, ?_, fun h' => absurd h' (by decide), fun _ => h2⟩
    rintro (h' | h') <;> exact absurd h' (by decide)

end CFSG.LieType.Chevalley
