module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.InnDiagThree
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EInputs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def InnDiagRankTwo : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeEps (K ⧸ center K) →
    ∀ E : Subgroup (MulAut K), IsElemAbelian 3 E → (∀ α ∈ E, IsInnDiagThree α) →
      Nat.card E ≤ 9

@[expose] def NoncyclicCentreRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsCatalogGroup (L ⧸ center L) → IsPGroup 3 (center L) → ¬ IsCyclic (center L) →
      4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)

@[expose] def AltTripleCoverAbelianBound : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → Nat.card (center L) = 3 →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty ((L ⧸ center L) ≃* alternatingGroup (Fin n))) →
    ∀ A : Subgroup L, IsPGroup 3 A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ 9

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
