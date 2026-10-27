module

public import CFSG.ClassicalInvolution.Asc77.AscT8X3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8X

variable (p f : ℕ) [Fact p.Prime]

@[expose] def W2CaseA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        DConnected (T8.layerFamQ Ω (z * t)) → False

@[expose] def W2CaseB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        ¬ DConnected (T8.layerFamQ Ω (z * t)) →
          ∃ A : Subgroup G, A ≤ (S : Subgroup G) ∧ A ≠ ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
            StronglyClosedIn A (S : Subgroup G)

variable {p f}


theorem w2core_of_cases (hA : W2CaseA p f) (hB : W2CaseB p f) : W2Core p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ hne
  by_cases hc : DConnected (T8.layerFamQ Ω (z * t))
  · exact (hA G Ω K J S R T W z t hs hdisc hμ hne hc).elim
  · exact hB G Ω K J S R T W z t hs hdisc hμ hne hc

theorem c26_13_sc_of_cases (hA : W2CaseA p f) (hB : W2CaseB p f) : C26_13_sc p f :=
  c26_13_sc_of_w2core (w2core_of_cases hA hB)

end T8X

end CFSG.ClassicalInvolution.Asc77
