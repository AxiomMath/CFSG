module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactParabolicThreeSylowSmall : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y) → ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ →
    Subgroup.normalizer (T : Set Y) ≤ J → J ≠ Subgroup.normalizer (T : Set Y) →
    (∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) →
    (∀ Q : Sylow 3 J, IsCyclic (Q : Subgroup J) → Nat.card Q ≤ 3) ∧
    (∀ u ∈ J, ∀ v ∈ J, orderOf u = 9 → orderOf v = 9 → Commute u v →
      Subgroup.zpowers u ⊓ Subgroup.zpowers v ≠ ⊥) ∧
    (∀ N B : Subgroup Y, N ≤ B → B ≤ J → J ≤ Subgroup.normalizer (N : Set Y) →
      J ≤ Subgroup.normalizer (B : Set Y) → Nat.Coprime 3 (Nat.card N) →
      (∀ b ∈ B, ∃ e : ℕ, b ^ 3 ^ e ∈ N) → (∀ j ∈ J, ∃ e : ℕ, j ^ 2 ^ e ∈ B) →
      ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧
    (IsMulCommutative ↥(CFSG.pCore 3 (↥J ⧸ primeComplementCore (G := ↥J) 3)) →
      ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U)

end CFSG.AGLEmbedding
