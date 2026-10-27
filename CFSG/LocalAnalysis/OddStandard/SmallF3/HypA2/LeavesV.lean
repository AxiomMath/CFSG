module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def FStarSimple (S : Type) [Group S] : Prop :=
  LieModel S .PSL 2 3 2 ∨ LieModel S .PSL 2 3 4 ∨ LieModel S .PSL 3 3 1 ∨ LieModel S .PSU 3 3 1 ∨
    SmallF3OmegaQuotient S

@[expose] def CentralDatum (K : Type) [Group K] : Prop :=
  ∃ (q₀ : ℕ) (N : Subgroup K) (z : K), Odd q₀ ∧ 5 ≤ q₀ ∧ orderOf z = 2 ∧ z ∈ center K ∧
    z ∈ N ∧ HarrisLit.IsSLTwoOver q₀ ↥N ∧ TypU K

@[expose] def NoncentralDatum (K : Type) [Group K] : Prop :=
  ∃ (q₀ : ℕ) (T N : Subgroup K) (z : K), Odd q₀ ∧ 5 ≤ q₀ ∧ orderOf z = 2 ∧ z ∉ center K ∧
    z ∈ N ∧ N ≤ T ∧ T ≤ centralizer ({z} : Set K) ∧
    IsPComponent 2 (T.subgroupOf (centralizer ({z} : Set K))) ∧
    HarrisLit.IsSLTwoOver q₀ ↥N ∧ TypU ↥T

@[expose] def KDatum (K : Type) [Group K] : Prop :=
  CentralDatum K ∨ NoncentralDatum K

@[expose] def TableC : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    Catalog (K ⧸ center K) → ∀ σ : MulAut K, (∀ y, σ (σ y) = y) →
    ∀ X : Subgroup K, X ≤ fixedSubgroup σ → IsPComponent 2 (X.subgroupOf (fixedSubgroup σ)) →
      IsFStar ↥X → GH74.GLS.InChev2 (↥X ⧸ Open.fusionZStar ↥X) → ¬ IsFStar K →
      HarrisLit.IsSimpleChevalleyOver 3 (K ⧸ center K) ∨ IsResidualA2 K

@[expose] def CoverDatum : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) → center K ≠ ⊥ →
    FStarSimple (K ⧸ center K) → ¬ IsFStar K → CentralDatum K

@[expose] def Chev3Datum : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) →
    HarrisLit.IsSimpleChevalleyOver 3 (K ⧸ center K) → ¬ FStarSimple (K ⧸ center K) →
    ∀ σ : MulAut K, (∀ y, σ (σ y) = y) →
    ∀ X : Subgroup K, X ≤ fixedSubgroup σ → IsPComponent 2 (X.subgroupOf (fixedSubgroup σ)) →
      IsFStar ↥X → (center K = ⊥ ∧ LieModel K .PSL 2 3 8) ∨ KDatum K

@[expose] def TwoA7RankOne : Prop :=
  ∀ (J : Type) [Group J] [Finite J], GH74.GLS.IsDoubleCoverOfAlt (J ⧸ pPrimeCore 2 J) 7 →
    CFSG.pRank 2 J ≤ 1

structure Leaves1 : Prop where
  tableC : TableC
  coverDatum : CoverDatum
  chev3Datum : Chev3Datum
  twoA7RankOne : TwoA7RankOne

end CFSG.OddStandard.SmallF3.HypA2
