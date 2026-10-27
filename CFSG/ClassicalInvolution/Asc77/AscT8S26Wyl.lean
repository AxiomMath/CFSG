module

public import CFSG.ClassicalInvolution.Asc77.AscP1Strong
public import CFSG.ClassicalInvolution.Asc77.WP2Thm8

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C26_13_sc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W →
        ∃ A : Subgroup G, A ≤ (S : Subgroup G) ∧ A ≠ ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
          StronglyClosedIn A (S : Subgroup G)

variable {p f}

theorem c26_13_of_sc (h : C26_13_sc p f) : C26_13 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hD4
  obtain ⟨A, hAS, hA1, hAab, hsc⟩ := h G Ω K J S R T W z t hs hdisc hD4
  exact (l17_8 (p := p) (f := f)) G Ω K hs.stand S A hAS hA1 hAab hsc

end CFSG.ClassicalInvolution.Asc77
