module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open scoped MatrixGroups

@[expose] def KFact278L34 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X Q B U Y : Subgroup A),
    CFSG.Open.IsKGroup ↥X → CFSG.Open.pRank 3 X = 2 →
    CFSG.ABGLocalTools.IsSylowOf 3 Q X → IsCyclic (Subgroup.center ↥Q) →
    B ≤ Q → IsElemAbelian 3 B → Nat.card B = 9 →
    U ≤ Q → IsElemAbelian 3 U → Nat.card U = 9 →
    (∀ g ∈ X, B.map (MulAut.conj g).toMonoidHom ≠ U) →
    (∀ w ∈ Q, orderOf w = 3 → (∀ q ∈ Q, q * w = w * q) →
      ∀ g ∈ X, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w) →
    Y ≤ X → Y ≠ X →
    (∀ R : Subgroup A, R ≤ U → 1 ≤ CFSG.Open.pRank 3 R → normalizer (R : Set A) ⊓ X ≤ Y) →
    (∀ R : Subgroup A, R ≤ Q → 2 ≤ CFSG.Open.pRank 3 R → normalizer (R : Set A) ⊓ X ≤ Y) →
    ∃ K : Subgroup A, K ≤ X ∧ X ≤ normalizer (K : Set A) ∧ ⁅K, K⁆ = K ∧
      K ⊓ rankThreePrimeCore 3 X < K ∧
      (∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ rankThreePrimeCore 3 X ≤ N →
        N = K ⊓ rankThreePrimeCore 3 X ∨ N = K) ∧
      X ≤ (Y ⊔ K) ⊔ rankThreePrimeCore 3 X ∧
      Nonempty (Kbar K ≃* PSL(3, GaloisField 2 2)) ∧
      ∀ S : Subgroup A, IsTwoInvariantIn B X S → Y ⊔ S ≠ X →
        (rankThreePrimeCore 3 X).relIndex S ≤ 2

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
