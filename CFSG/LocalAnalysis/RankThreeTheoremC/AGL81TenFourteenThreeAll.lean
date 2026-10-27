module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable (G : Type) [Group G] [Finite G]

@[expose] def AGL81TenFourteenTwoPerfect : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H₁ R₁ : Subgroup G), D1Escape p P M H₁ R₁ →
    ∀ a : G, a ∈ M → orderOf a = p → ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ p M U) →
    ∀ I : Subgroup G, IsTwoPrimeComponent (Subgroup.centralizer ({a} : Set G) ⊓ M) I →
      p ∣ Nat.card I → p = 5

@[expose] def AGL81TenFourteenTwoPerfectA5 : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H₁ R₁ : Subgroup G), D1Escape p P M H₁ R₁ →
    ∀ a : G, a ∈ M → orderOf a = p → ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ p M U) →
    ∀ I : Subgroup G, IsTwoPrimeComponent (Subgroup.centralizer ({a} : Set G) ⊓ M) I →
      p ∣ Nat.card I → p = 5 ∧ Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* alternatingGroup (Fin 5))

variable {G}

theorem agl81TenFourteenTwoPerfect_of_A5 (h : AGL81TenFourteenTwoPerfectA5 G) :
    AGL81TenFourteenTwoPerfect G := fun hS p P M H₁ R₁ hesc a ha hao hC hU I hI hp =>
  (h hS p P M H₁ R₁ hesc a ha hao hC hU I hI hp).1

theorem agl81TenFourteenTwoThree_of_perfect (h : AGL81TenFourteenTwoPerfect G) :
    AGL81TenFourteenTwoThree G := by
  intro hS P M H₁ R₁ hesc a ha hao hC hU I hI h3
  exact absurd (h hS 3 P M H₁ R₁ hesc a ha hao hC hU I hI h3) (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC
