module

public import CFSG.ClassicalInvolution.Asc77.AscIHThm4
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedExactStmt

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Thm5Below (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ∀ Ω : Set (Subgroup G),
      HypOmegaMod p f Ω → classicalInvolutionOddCore G = ⊥ →
        ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ z : G, IsUniqueInvolution K z →
          ∀ A : Subgroup G, IsElemAbelian2 A 2 → A ≤ K ⊔ J → z ∈ A → alphaOf A = ⊥

@[expose] def Thm6TypedBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaMod p f Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → Disconnected.DEdgeless Ω →
          HasLieType p f Ω .PSL 3 ∨ HasLieType p f Ω .PSU 3 ∨ HasLieType p f Ω .G2 0 ∨
            HasLieType p f Ω .trialityD4 0

@[expose] def Thm7TypedBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaMod p f Ω → (∀ J ∈ Ω, AEmpty Ω J) →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
          ∀ K ∈ Ω, (∃ K' ∈ twinSet Ω K, K' ≠ K) →
            ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ HasOrthType p f Ω d ε

@[expose] def Thm8TypedBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaMod p f Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → ¬ Disconnected.DEdgeless Ω →
          ¬ Disconnected.DConnected Ω →
            ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthType p f Ω d ε

@[expose] def MuTableBelow (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], Nat.card G < n →
      ∀ Ω : Set (Subgroup G), HypOmegaMod p f Ω → (∀ J ∈ Ω, AEmpty Ω J) → Ω.Nonempty →
        (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) → ∀ W ∈ WSet Ω,
          (MuIsoZ2 Ω W ↔ (if piSign p f then HasLieType p f Ω .PSU 3
              else HasLieType p f Ω .PSL 3)) ∧
          (MuIsoS3 Ω W ↔ ((if piSign p f then HasLieType p f Ω .PSL 3
              else HasLieType p f Ω .PSU 3) ∨ HasLieType p f Ω .G2 0 ∨
              HasLieType p f Ω .trialityD4 0)) ∧
          (MuIsoE4 Ω W ↔ (HasOrthType p f Ω 5 true ∨
              HasOrthType p f Ω 6 (!piSign p f) ∨
              (if piSign p f then HasLieType p f Ω .PSU 5 else HasLieType p f Ω .PSL 5))) ∧
          (MuIsoS4 Ω W ↔ (HasOrthType p f Ω 6 (piSign p f) ∨ HasOrthType p f Ω 7 true ∨
              HasOrthType p f Ω 8 false)) ∧
          (HasOrthType p f Ω 8 true → MuIsoWylD4 Ω W) ∧
          (¬ Disconnected.DConnected Ω → MuIsoWylD4 Ω W → HasOrthType p f Ω 8 true)

structure IH8 (n : ℕ) : Prop where
  thm2 : Thm2Below p f n
  thm4 : Thm4Below p f n
  thm5 : Thm5Below p f n
  thm6 : Thm6TypedBelow p f n
  thm7 : Thm7TypedBelow p f n
  thm8 : Thm8TypedBelow p f n
  muTable : MuTableBelow p f n
  thm3 : T3Typed.Thm3TypedBelowExact p f n

@[expose] def IH8All (n : ℕ) : Prop :=
  ∀ e : ℕ, 5 ≤ p ^ e → IH8 p e n

@[expose] def IH8Rest : Prop :=
  ∀ n : ℕ, CITBelowU p f n →
    Thm5Below p f n ∧ Thm6TypedBelow p f n ∧ Thm7TypedBelow p f n ∧ Thm8TypedBelow p f n ∧
      MuTableBelow p f n ∧ T3Typed.Thm3TypedBelowExact p f n

variable {p f}

theorem ih8_of_rest (h : IH8Rest p f) {n : ℕ} (hn : CITBelowU p f n) : IH8 p f n :=
  have h24 := ihInterface (p := p) (f := f) n hn
  have h5 := h n hn
  ⟨h24.2, h24.1, h5.1, h5.2.1, h5.2.2.1, h5.2.2.2.1, h5.2.2.2.2.1, h5.2.2.2.2.2⟩

theorem ih8All_of_rest (h : ∀ e : ℕ, 5 ≤ p ^ e → IH8Rest p e) {n : ℕ} (hn : CITBelowAll p n) :
    IH8All p n :=
  fun e he => ih8_of_rest (h e he) (hn e he)

end CFSG.ClassicalInvolution.Asc77
