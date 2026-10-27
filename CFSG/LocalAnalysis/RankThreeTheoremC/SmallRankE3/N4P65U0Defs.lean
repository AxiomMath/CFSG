module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4P65Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def StepP65OddSevenU0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
    ∀ (p : ℕ), 7 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z → ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M →
        Nat.Coprime p (Nat.card F) → Odd (Nat.card F) →
          zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

@[expose] def StepP65OddE3U0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
    ∀ (p : ℕ), 5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G), SmallRankSituation G p P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z → ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M →
        Nat.Coprime p (Nat.card F) → Odd (Nat.card F) →
          zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

theorem stepP65OddE3U0_of_five_seven (h5 : StepP65OddFive) (h7 : StepP65OddSevenU0) :
    StepP65OddE3U0 := by
  intro G _ _ hS hD1 hU0 p hp5 P M hsit x z hx hz F hF1 hFM hFcop hFodd hBF
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  by_cases h : p = 5
  · subst h
    exact h5 G hS hD1 P M hsit x z hx hz F hF1 hFM hFcop hFodd hBF
  · have h6 : p ≠ 6 := by
      rintro rfl
      norm_num at hprime
    exact h7 G hS hD1 hU0 p (by omega) P M hsit x z hx hz F hF1 hFM hFcop hFodd hBF

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
