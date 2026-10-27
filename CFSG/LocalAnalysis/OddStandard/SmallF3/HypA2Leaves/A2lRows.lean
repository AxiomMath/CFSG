module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lDatum

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.OddStandard.SmallF3.HypA2 (FStarSimple IsFStar KDatum Chev3Datum)

@[expose] def a2lRowPSL : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), 3 ≤ n → (2 ≤ f ∨ 5 ≤ n) →
    LieModel X .PSL n 3 f → a2lDatum X

@[expose] def a2lRowPSU : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), 3 ≤ n → (2 ≤ f ∨ 5 ≤ n) →
    LieModel X .PSU n 3 f → a2lDatum X

@[expose] def a2lRowPSp : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), 2 ≤ n → (2 ≤ f ∨ 3 ≤ n) →
    LieModel X .PSp n 3 f → a2lDatum X

@[expose] def a2lRowPOmegaOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), 3 ≤ n → (2 ≤ f ∨ 4 ≤ n) →
    LieModel X .POmegaOdd n 3 f → a2lDatum X

@[expose] def a2lRowPOmegaPlus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), 4 ≤ n → (2 ≤ f ∨ 5 ≤ n) →
    LieModel X .POmegaPlus n 3 f → a2lDatum X

@[expose] def a2lRowPOmegaMinus : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), 4 ≤ n → (2 ≤ f ∨ 5 ≤ n) →
    LieModel X .POmegaMinus n 3 f → a2lDatum X

@[expose] def a2lRowG2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 2 ≤ f → LieModel X .G2 0 3 f → a2lDatum X

@[expose] def a2lRowF4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X .F4 0 3 f → a2lDatum X

@[expose] def a2lRowE6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X .E6 0 3 f → a2lDatum X

@[expose] def a2lRowE7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X .E7 0 3 f → a2lDatum X

@[expose] def a2lRowE8 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X .E8 0 3 f → a2lDatum X

@[expose] def a2lRowTwistedE6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X .twistedE6 0 3 f → a2lDatum X

@[expose] def a2lRowTrialityD4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X .trialityD4 0 3 f → a2lDatum X

structure a2lRows : Prop where
  psl : a2lRowPSL
  psu : a2lRowPSU
  psp : a2lRowPSp
  oOdd : a2lRowPOmegaOdd
  oPlus : a2lRowPOmegaPlus
  oMinus : a2lRowPOmegaMinus
  g2 : a2lRowG2
  f4 : a2lRowF4
  e6 : a2lRowE6
  e7 : a2lRowE7
  e8 : a2lRowE8
  twistedE6 : a2lRowTwistedE6
  trialityD4 : a2lRowTrialityD4

@[expose] def a2lChev3On (P : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    HarrisLit.IsSimpleChevalleyOver 3 (K ⧸ center K) → ¬ FStarSimple (K ⧸ center K) →
    P (K ⧸ center K) → ∀ σ : MulAut K, (∀ y, σ (σ y) = y) →
    ∀ X : Subgroup K, X ≤ fixedSubgroup σ → IsPComponent 2 (X.subgroupOf (fixedSubgroup σ)) →
      IsFStar ↥X → (center K = ⊥ ∧ LieModel K .PSL 2 3 8) ∨ KDatum K

structure a2lChev3Exceptions : Prop where
  l2 : a2lChev3On fun S _ => ∃ e : ℕ, LieModel S .PSL 2 3 e
  g23 : a2lChev3On fun S _ => LieModel S .G2 0 3 1
  ree : a2lChev3On fun S _ => ∃ f : ℕ, LieModel S .twistedG2 0 3 f

end CFSG.OddStandard.SmallF3.HypA2Leaves
