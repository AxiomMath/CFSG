module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def TwelveFourStepA (M : Subgroup G) (d : ℕ) : Prop :=
  3 ∉ sigmaSet G M ∧ CFSG.Open.pRank 3 M ≤ 3 ∧ 5 ≤ d

@[expose] def TwelveFourASevenLeX (M : Subgroup G) (p : ℕ) (H L : Subgroup G) : Prop :=
  NineThreeFive M L → CFSG.ComponentClassification.AS76b.oUpperTwo (H ⊓ L) ≤ xSub p M H

@[expose] def TwelveFourYCentJ (M H L : Subgroup G) (d : ℕ) : Prop :=
  ∀ b ∈ oPPrimeHull d (H ⊓ M), ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)

@[expose] def TwelveFourTenThreeThree (M H L : Subgroup G) : Prop :=
  ∀ b ∈ H ⊓ M, b ∈ normalizer (L : Set G) → Odd (orderOf b) →
    (∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
    (∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 L) ∨
    (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
      IsParabolicTwo (barM M L) (barM M (H ⊓ L)) ∧
      ¬ CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 (barM M (H ⊓ L))) (barM M L)) ∨
    NineThreeFive M L

@[expose] def TwelveFourYCentL (M H L : Subgroup G) (d : ℕ) : Prop :=
  (∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 M) ∧
  ∀ W : Subgroup G, W ≤ H ⊓ M → W ≤ L ⊔ pCoreOf 2 M →
    ∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ w ∈ W,
      y * w * y⁻¹ * w⁻¹ ∈ pCoreOf 2 (oPPrimeHull d (H ⊓ M))

@[expose] def TwelveFourBlockRank (M H L : Subgroup G) (d : ℕ) : Prop :=
  CFSG.Open.pRank 3 (barM M L) ≤ 2 ∧ ¬ d ∣ Nat.card (L ⊓ H : Subgroup G)

@[expose] def TwelveFourWitness (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ)
    (W : Subgroup G) : Prop :=
  Nat.card W = 3 ∧ W ≤ xSub p M H ∧
    (∀ y ∈ oPPrimeHull d (H ⊓ M), ∀ w ∈ W,
      y * w * y⁻¹ * w⁻¹ ∈ pCoreOf 2 (oPPrimeHull d (H ⊓ M))) ∧
    2 ≤ CFSG.Open.pRank d (M ⊓ centralizer (W : Set G))

structure TwelveFourBlockFacts (M H L : Subgroup G) : Prop where
  three_dvd : 3 ∣ Nat.card (L ⊓ H : Subgroup G)
  cZero_nonempty : ¬ NineThreeFive M L → (cZero (H ⊓ L)).Nonempty
  three_dvd_oUpperTwo : ∀ I ∈ cZero (H ⊓ L),
    3 ∣ Nat.card (CFSG.ComponentClassification.AS76b.oUpperTwo I)
  aSeven_primes : NineThreeFive M L → ∀ r : ℕ, r.Prime →
    r ∣ Nat.card (H ⊓ L : Subgroup G) → r = 2 ∨ r = 3
  order_three : ∃ t ∈ barM M L, orderOf t = 3 ∧
    t ∉ centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  rank_table : CFSG.Open.pRank 3 (barM M L) ≤ 3 → ∀ d : ℕ, d.Prime → 5 ≤ d →
    ¬ d ∣ Nat.card (L ⊓ H : Subgroup G) →
      CFSG.Open.pRank d (barM M L) + 1 ≤ max 2 (CFSG.Open.pRank 3 (barM M L)) ∧
        ¬ d ∣ Nat.card (Subgroup.center ↥(barM M L))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
