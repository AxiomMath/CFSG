module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCoreDefs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

@[expose] def HeisARankFacts : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L → Odd (Nat.card (Subgroup.center L)) →
    OddRankLeThree L → IsSimpleGroup (L ⧸ Subgroup.center L) →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f → 2 ≤ n → 1 ≤ f →
      (L ⧸ Subgroup.center L ≃* StatedProj (StatedSL n K)) →
      ∀ p : ℕ, p.Prime → 5 ≤ p →
        ¬ p ∣ Nat.gcd n (2 ^ f - 1) ∧ n / orderOf ((2 ^ f : ℕ) : ZMod p) < p ∧
          ¬ p ∣ Nat.card (Subgroup.center L)

@[expose] def HeisURankFacts : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L → Odd (Nat.card (Subgroup.center L)) →
    OddRankLeThree L → IsSimpleGroup (L ⧸ Subgroup.center L) →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 2 → 3 ≤ n → 1 ≤ f →
      (L ⧸ Subgroup.center L ≃* StatedProj (StatedSU n (2 ^ f) K)) →
      ∀ p : ℕ, p.Prime → 5 ≤ p →
        (¬ p ∣ Nat.gcd n (2 ^ f + 1) ∧ n / orderOf (-((2 ^ f : ℕ) : ZMod p)) < p ∧
          ¬ p ∣ Nat.card (Subgroup.center L)) ∨
        (p = 5 ∧ n = 5 ∧ f = 2 ∧ Subgroup.center L = ⊥)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
