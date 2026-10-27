module

public import CFSG.LocalAnalysis.RankThreeTheoremC.StrongEmbeddingCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSetup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def UniquenessAt (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M : Subgroup G) : Prop :=
  (rankThreeGamma 1 p (P : Subgroup G) ≤ M ∨ rankThreeClauseB M (P : Subgroup G) p ∨
      (p = 3 ∧ rankThreeClauseC M (P : Subgroup G))) ∧
    ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M

@[expose] def LargerPrimesUnique (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ f ∈ rankThreeSigmaA G, p < f → ∀ (P : Sylow f G) (M : Subgroup G), IsCoreMaxLocal f P M →
    UniquenessAt G f P M

@[expose] def GenericCase (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → (∃ y : G, IsLargeObstruction p M y) →
      LargerPrimesUnique G p → UniquenessAt G p P M

@[expose] def SmallRankCase (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → (∀ y : G, ¬ IsLargeObstruction p M y) →
      LargerPrimesUnique G p → UniquenessAt G p P M

theorem uniquenessAt_of_cases (hS : Setting G) (hD2 : TheoremD2 G) (hU0 : FullCoreLocal G)
    (hgen : GenericCase G) (hsmall : SmallRankCase G) :
    ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
      UniquenessAt G p P M := by
  suffices h : ∀ n p, Nat.card G - p = n → p ∈ rankThreeSigmaA G → ∀ (P : Sylow p G)
      (M : Subgroup G), IsCoreMaxLocal p P M → UniquenessAt G p P M from
    fun p hp => h _ p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn hp P M hM
    have hIH : LargerPrimesUnique G p := fun f hf hpf =>
      ih (Nat.card G - f)
        (by have := Nat.le_of_dvd Nat.card_pos (sigmaA_dvd_card f hf); omega) f rfl hf
    by_cases hΓ : rankThreeGamma 1 p (P : Subgroup G) ≤ M
    · exact ⟨Or.inl hΓ, fun H hH h2 => le_of_two_le_pRank_of_gamma_one_le hS hD2 hU0 hp hM hΓ hH h2⟩
    · by_cases hempty : ∀ y : G, ¬ IsLargeObstruction p M y
      · exact hsmall p hp P M hM hΓ hempty hIH
      · push Not at hempty
        exact hgen p hp P M hM hΓ hempty hIH

theorem nonStrongEmbeddingCase_of_cases (hS : Setting G) (hD2 : TheoremD2 G)
    (hU0 : FullCoreLocal G) (hgen : GenericCase G) (hsmall : SmallRankCase G) :
    NonStrongEmbeddingCase G := fun _ =>
  ⟨fun p hp P M hM => (uniquenessAt_of_cases hS hD2 hU0 hgen hsmall p hp P M hM).1,
    fun p hp P M hM => (uniquenessAt_of_cases hS hD2 hU0 hgen hsmall p hp P M hM).2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
