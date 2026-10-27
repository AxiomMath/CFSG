module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFiveReduction

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.PreuniquenessRankFour.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def StrongOrExceptionalAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (P : Sylow p G) (M : Subgroup G), D1Local p P M →
    GLBCore p 2 (P : Subgroup G) ≤ M →
      ((p ∣ Nat.card M ∧ ∀ g : G, g ∉ M → ¬ p ∣ Nat.card (M ⊓ GLBConj g M : Subgroup G)) ∨
        (Group.IsSolvable M ∧ IsMulCommutative (P : Subgroup G) ∧
          ∃ P₀ : Subgroup G, GLBClauseTwo M P P₀ p))

@[expose] def ConfinementNonstrongAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (P : Sylow p G) (M : Subgroup G), D1Local p P M → ¬ GLBStronglyEmbedded p M →
    ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ Open.pRank p (H ⊓ M) → H ≤ M

@[expose] def ThmCAt (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  StrongOrExceptionalAt G p ∧ ConfinementNonstrongAt G p

@[expose] def ThmCStepFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Open.IsKProper G → IsCharTwoType G → 4 ≤ evenRank G → GLBPreuniqueness G →
      ∀ p : ℕ, 5 ≤ p → (∀ q : ℕ, p < q → ThmCAt G q) → ThmCAt G p

variable {G : Type} [Group G] [Finite G]

theorem thmCAt_of_card_lt {p : ℕ} (hp : Nat.card G < p) : ThmCAt G p := by
  have hv : ∀ (P : Sylow p G) (M : Subgroup G), ¬ D1Local p P M := fun P M hloc =>
    absurd (Nat.le_of_dvd Nat.card_pos hloc.beta.2.2.1) (by omega)
  exact ⟨fun P M hloc _ => absurd hloc (hv P M), fun P M hloc _ => absurd hloc (hv P M)⟩

theorem thmCAt_all_of_step
    (step : ∀ p : ℕ, 5 ≤ p → (∀ q : ℕ, p < q → ThmCAt G q) → ThmCAt G p) :
    ∀ p : ℕ, 5 ≤ p → ThmCAt G p := by
  have key : ∀ k p : ℕ, Nat.card G + 1 - p = k → 5 ≤ p → ThmCAt G p := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro p hk hp
      by_cases hbig : Nat.card G < p
      · exact thmCAt_of_card_lt hbig
      · refine step p hp fun q hq => ?_
        by_cases hqbig : Nat.card G < q
        · exact thmCAt_of_card_lt hqbig
        · exact ih (Nat.card G + 1 - q) (by omega) q rfl (by omega)
  exact fun p hp => key _ p rfl hp

theorem strongOrExceptionalFive_of_thmCAt (h : ∀ p : ℕ, 5 ≤ p → ThmCAt G p) :
    StrongOrExceptionalFive G :=
  fun p P M hp5 hloc hcore => (h p hp5).1 P M hloc hcore

theorem confinementNonstrongFive_of_thmCAt (h : ∀ p : ℕ, 5 ≤ p → ThmCAt G p) :
    ConfinementNonstrongFive G :=
  fun p P M hp5 hloc hns H hH hrank => (h p hp5).2 P M hloc hns H hH hrank

theorem dichotomyRank4Five_of_step (hstep : ThmCStepFive) : DichotomyRank4Five :=
  fun G _ _ _ hnonab hK hchar he hpre =>
    strongOrExceptionalFive_of_thmCAt
      (thmCAt_all_of_step (hstep G hnonab hK hchar he hpre))

theorem e2NonstrongRank4Five_of_step (hstep : ThmCStepFive) : E2NonstrongRank4Five :=
  fun G _ _ _ hnonab hK hchar he hpre =>
    confinementNonstrongFive_of_thmCAt
      (thmCAt_all_of_step (hstep G hnonab hK hchar he hpre))

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
