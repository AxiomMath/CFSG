module

public import CFSG.ClassicalInvolution.Uniform.UThmStmtA

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups commutatorElement

@[expose] def Thm6TypedBelowU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → Disconnected.DEdgeless Ω →
          HasLieTypeU p f Ω .PSL 3 ∨ HasLieTypeU p f Ω .PSU 3 ∨ HasLieTypeU p f Ω .G2 0 ∨
            HasLieTypeU p f Ω .trialityD4 0 ∨ HasM11TypeU p f Ω

@[expose] def Thm7TypedBelowU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → (∀ J ∈ Ω, AEmpty Ω J) →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ K ∈ Ω, (∃ K' ∈ twinSet Ω K, K' ≠ K) →
            ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ HasOrthTypeU p f Ω d ε

@[expose] def Thm8TypedBelowU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → ¬ Disconnected.DEdgeless Ω →
          ¬ Disconnected.DConnected Ω →
            ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthTypeU p f Ω d ε

@[expose] def MuTableBelowU (p f : ℕ) [Fact p.Prime] (n : ℕ) : Prop :=
  p ≠ 2 → 3 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaModU (.sl2 p f) Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → ∀ W ∈ WSet Ω,
          (MuIsoZ2 Ω W ↔ ((if piSign p f then HasLieTypeU p f Ω .PSU 3
              else HasLieTypeU p f Ω .PSL 3) ∨ HasM11TypeU p f Ω)) ∧
          (MuIsoS3 Ω W ↔ ((if piSign p f then HasLieTypeU p f Ω .PSL 3
              else HasLieTypeU p f Ω .PSU 3) ∨ HasLieTypeU p f Ω .G2 0 ∨
              HasLieTypeU p f Ω .trialityD4 0)) ∧
          (MuIsoE4 Ω W ↔ (HasOrthTypeU p f Ω 5 true ∨
              HasOrthTypeU p f Ω 6 (!piSign p f) ∨
              (if piSign p f then HasLieTypeU p f Ω .PSU 5 else HasLieTypeU p f Ω .PSL 5))) ∧
          (MuIsoS4 Ω W ↔ (HasOrthTypeU p f Ω 6 (piSign p f) ∨ HasOrthTypeU p f Ω 7 true ∨
              HasOrthTypeU p f Ω 8 false)) ∧
          (HasOrthTypeU p f Ω 8 true → MuIsoWylD4 Ω W) ∧
          (¬ Disconnected.DConnected Ω → MuIsoWylD4 Ω W → HasOrthTypeU p f Ω 8 true)

variable {p f : ℕ} [Fact p.Prime]

theorem thm6TypedBelowU_iff (h3 : p ^ f ≠ 3) (n : ℕ) :
    Thm6TypedBelowU p f n ↔ Thm6TypedBelow p f n := by
  unfold Thm6TypedBelowU Thm6TypedBelow
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq, hasLieTypeU_iff h3, not_hasM11TypeU h3, or_false]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

theorem thm7TypedBelowU_iff (h3 : p ^ f ≠ 3) (n : ℕ) :
    Thm7TypedBelowU p f n ↔ Thm7TypedBelow p f n := by
  unfold Thm7TypedBelowU Thm7TypedBelow
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq, hasOrthTypeU_iff h3]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

theorem thm8TypedBelowU_iff (h3 : p ^ f ≠ 3) (n : ℕ) :
    Thm8TypedBelowU p f n ↔ Thm8TypedBelow p f n := by
  unfold Thm8TypedBelowU Thm8TypedBelow
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq, hasOrthTypeU_iff h3]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

theorem muTableBelowU_iff (h3 : p ^ f ≠ 3) (n : ℕ) :
    MuTableBelowU p f n ↔ MuTableBelow p f n := by
  unfold MuTableBelowU MuTableBelow
  by_cases hp2 : p = 2
  · simp [hp2]
  by_cases hq : 5 ≤ p ^ f
  · have hq3 : 3 ≤ p ^ f := by omega
    simp only [ne_eq, hp2, not_false_eq_true, hq3, hq, forall_const,
      hypOmegaModU_iff_hypOmegaMod hp2 hq, hasLieTypeU_iff h3, hasOrthTypeU_iff h3,
      not_hasM11TypeU h3, or_false]
  · simp [hp2, hq, not_three_le_of_lt_five hp2 h3 hq]

end CFSG.ClassicalInvolution.Uniform
