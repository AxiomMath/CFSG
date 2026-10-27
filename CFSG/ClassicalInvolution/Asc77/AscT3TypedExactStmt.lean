module

public import CFSG.ClassicalInvolution.Asc77.AscT3Stmt

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Typed

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Thm3CommBelowExact (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → classicalInvolutionOddCore G = ⊥ →
      ∀ Ω : Set (Subgroup G), HypOmegaMod p f Ω → ∀ K ∈ Ω, ¬ AEmpty Ω K →
        aStar Ω K = vStar Ω K ∧
          ∀ L ∈ Ω, L ∉ vStar Ω K → ∀ M ∈ vStar Ω K, ⁅L, M⁆ ≤ oddCoreOf L ⊓ oddCoreOf M

@[expose] def Thm3LieBelowExact (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f →
    ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → classicalInvolutionOddCore G = ⊥ →
      ∀ Ω : Set (Subgroup G), HypOmegaMod p f Ω → ∀ K ∈ Ω, ¬ AEmpty Ω K →
        SectionLieType p f Ω (omegaGen (aStar Ω K)) .G2 0

@[expose] def Thm3TypedBelowExact (n : ℕ) : Prop :=
  Thm3CommBelowExact p f n ∧ Thm3LieBelowExact p f n

end CFSG.ClassicalInvolution.Asc77.T3Typed
