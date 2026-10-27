module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G3At

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Vocabulary

variable {Y : Type} [Group Y]

@[expose] def TwinOrbits (Φ : Set (Subgroup Y)) (K : Subgroup Y) : Prop :=
  ∀ L ∈ Φ, ∃ g : Y, ∃ J ∈ twinSet Φ K, conjSub g J = L

@[expose] def NoNormalTwo (Y : Type) [Group Y] : Prop :=
  ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥

@[expose] def SubClass (Φ : Set (Subgroup Y)) (K T : Subgroup Y) : Prop :=
  ∀ L ∈ Φ, ∃ t ∈ T, conjSub t K = L

@[expose] def FStarSimple (Y : Type) [Group Y] : Prop :=
  IsSimpleGroup ↥(genFittingFStar Y) ∧ ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a

@[expose] def InnerIH (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) : Prop :=
  ∀ Φ' : Set (Subgroup Y), Φ'.ncard < Φ.ncard → TypeRHyp Φ' → ∀ K ∈ Φ', ¬ AEmpty Φ' K →
    Thm3RConclG Φ' K

end Vocabulary

@[expose] def Thm3RLiftSub : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)), TypeRHyp Φ → ∀ K ∈ Φ, ¬ AEmpty Φ K →
    Thm3RConclG (restrictFamily Φ (omegaGen Φ)) (K.subgroupOf (omegaGen Φ)) → Thm3RConclG Φ K

@[expose] def Thm3RFStar : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y), TypeRHyp Φ → K ∈ Φ →
    classicalInvolutionOddCore Y = ⊥ → omegaGen Φ = ⊤ → TwinOrbits Φ K → NoNormalTwo Y →
      FStarSimple Y

section Step


structure StepIH (m : ℕ) : Prop where
  cit : CIT3Below (m + 1)
  pkg : TL4.TightBelowRPlus 3 (m + 1)
  below : Thm3RBelowG m

structure Ctx (m : ℕ) (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y) :
    Prop where
  ih : StepIH m
  card : Nat.card Y = m
  inner : InnerIH Y Φ
  hyp : TypeRHyp Φ
  mem : K ∈ Φ
  notEmpty : ¬ AEmpty Φ K
  odd : classicalInvolutionOddCore Y = ⊥
  gen : omegaGen Φ = ⊤

@[expose] def Thm3RTwoOrbit (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y), Ctx m Y Φ K →
    ¬ TwinOrbits Φ K → Thm3RConclG Φ K

@[expose] def Thm3RThmB (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y), Ctx m Y Φ K →
    TwinOrbits Φ K → ∀ z : Y, IsUniqueInvolution K z → TightInO2 z → Thm3RConclG Φ K

@[expose] def Thm3RO2Lift (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y), Ctx m Y Φ K →
    TwinOrbits Φ K → (∀ z : Y, IsUniqueInvolution K z → ¬ TightInO2 z) → ¬ NoNormalTwo Y →
      Thm3RConclG Φ K

@[expose] def Thm3RTwoClass (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y), Ctx m Y Φ K →
    TwinOrbits Φ K → NoNormalTwo Y → FStarSimple Y → ¬ SubClass Φ K (genFittingFStar Y) →
      ¬ CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .G2 0 3 1 → Thm3RConclG Φ K

@[expose] def Thm3RTwoClassG23 (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y), Ctx m Y Φ K →
    TwinOrbits Φ K → NoNormalTwo Y → FStarSimple Y → ¬ SubClass Φ K (genFittingFStar Y) →
      CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .G2 0 3 1 → Thm3RConclG Φ K

@[expose] def Thm3RStdSimple (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] [IsSimpleGroup Y], Nat.card Y = m → StepIH m →
    ∀ K : Subgroup Y, TypeRHyp (CoreAssembly.conjClass K) →
      ¬ AEmpty (CoreAssembly.conjClass K) K → False

@[expose] def Thm3RStdOuter (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Φ : Set (Subgroup Y)) (K : Subgroup Y), Ctx m Y Φ K →
    NoNormalTwo Y → FStarSimple Y → SubClass Φ K (genFittingFStar Y) → genFittingFStar Y ≠ ⊤ →
      False

end Step

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step
