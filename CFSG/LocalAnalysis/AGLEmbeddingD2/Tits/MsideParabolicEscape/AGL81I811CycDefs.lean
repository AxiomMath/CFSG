module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2

@[expose] def AGL81I811Cyc : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G →
    ∀ M : Subgroup G, GLBStronglyEmbedded 3 M → ∀ H : Subgroup G, H ≠ ⊤ →
      (∀ X : Subgroup G, X ≤ H ⊓ M → IsPGroup 3 X → IsCyclic X) →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥(H ⊓ M) → ∀ T : Subgroup G, IsSylowTwoOf T (H ⊓ M) →
        (∀ S : Subgroup G, S ≤ H → IsPGroup 2 S → Nat.card S ≤ 8 * Nat.card T) →
        IsSylowTwoOf T H

@[expose] def KFactCoprimeThreeTwoPart : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup S → ¬ 3 ∣ Nat.card S → 64 ∣ Nat.card S

@[expose] def KFactThreeRankOneOvergroup : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup K → (∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) →
    ∀ A W : Subgroup K, Nat.card A = 3 → Subgroup.normalizer (A : Set K) ≤ W →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥W → ¬ 16 ∣ W.index → Odd W.index

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
