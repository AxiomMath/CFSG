module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactThreeRankOneOvergroupL32 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Open.IsCatalogGroup K → (∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) →
    ∀ A W Y : Subgroup K, Nat.card A = 3 → Subgroup.normalizer (A : Set K) ≤ W → Y ≤ W →
      A ≤ Y → IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) → W = ⊤ ∨ ¬ 2 ∣ W.index

@[expose] def LThreeTwoCoreOdd : Prop :=
  ∀ (N : Type) [Group N] [Finite N], Open.IsKGroup N → ∀ I N₀ Y A : Subgroup N, I.Normal →
    ¬ 3 ∣ Nat.card I → Nat.card A = 3 → A ≤ Y → Y ≤ N₀ → IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) →
    I ⊓ Subgroup.centralizer (A : Set N) ≤ N₀ → ¬ 2 ∣ (I ⊓ N₀).relIndex I

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
