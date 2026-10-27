module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open CFSG.RankThree.PartOne.OutStructure (Inn)
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def PGoodOut (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∃ D : Subgroup (MulAut X), D.Normal ∧ Inn X ≤ D ∧
    (∀ δ ∈ D, ∀ k : ℕ, δ ^ (p ^ k) ∈ Inn X → δ ∈ Inn X) ∧
    ∀ α γ : MulAut X, (∃ k : ℕ, α ^ (p ^ k) ∈ D) → ⁅γ, α⁆ ∈ D

@[expose] def D4PGood : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p ℓ f : ℕ), p.Prime → 5 ≤ p →
    StatedClassicalModel X .POmegaPlus 4 ℓ f → PGoodOut p X

@[expose] def TorusLin : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L T : Subgroup Y) (n f p : ℕ), p.Prime → 5 ≤ p →
    CFSG.Open.IsQuasisimple ↥L → StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f →
    p ∣ Nat.gcd n (2 ^ f - 1) → IsSylowTwoOf T L →
    p ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y))

end CFSG.AGLEmbedding.TwoGenInner
