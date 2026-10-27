module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartOne.CTP.StrongPLinear
public import CFSG.RankThree.PartOne.CTP.FusionSound

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
open CFSG.RankThree.PartOne.CTP.Fus

@[expose] def SporadicBetaData (X : Type) [Group X] : Prop :=
  Nat.card (Outer X) ≤ 2 ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
    ¬ p ^ 3 ∣ Nat.card X ∨ (¬ p ^ 4 ∣ Nat.card X ∧ HasNoncommPair p X) ∨
      FusionGenerationOf X p

@[expose] def MonsterBetaData : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* Blueprint.NativeSporadic.Carrier .M) → SporadicBetaData T

end CFSG.AGLEmbedding
