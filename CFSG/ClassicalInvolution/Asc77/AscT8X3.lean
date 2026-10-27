module

public import CFSG.ClassicalInvolution.Asc77.AscT8S26Wyl
public import CFSG.ClassicalInvolution.Asc77.AscT8X1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T8X

variable (p f : ℕ) [Fact p.Prime]


@[expose] def W2Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoWylD4 Ω W → dComp Ω K ≠ dstarComp Ω K →
        ∃ A : Subgroup G, A ≤ (S : Subgroup G) ∧ A ≠ ⊥ ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
          StronglyClosedIn A (S : Subgroup G)

variable {p f}


theorem c26_13_sc_of_w2core (h : W2Core p f) : C26_13_sc p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hμ
  by_cases hcomp : dComp Ω K = dstarComp Ω K
  · exact (false_of_dComp_eq hs hdisc hcomp hμ).elim
  · exact h G Ω K J S R T W z t hs hdisc hμ hcomp

end T8X

end CFSG.ClassicalInvolution.Asc77
