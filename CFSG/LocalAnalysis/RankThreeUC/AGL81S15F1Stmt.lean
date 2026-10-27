module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsLThreeTwo)

@[expose] def F1For (K : Type) [Group K] [Finite K] : Prop :=
  IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup K →
    (∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) →
    ∀ A W Y : Subgroup K, Nat.card A = 3 → Subgroup.normalizer (A : Set K) ≤ W → Y ≤ W →
      A ≤ Y → IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) → W ≠ ⊤ →
      ∀ S : Subgroup K, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → S ≤ W →
        Subgroup.normalizer (S : Set K) ≤ W

@[expose] def F1Core (G : Type) [Group G] [Finite G] : Prop :=
  (∀ X : Subgroup G, IsPGroup 3 X → IsCyclic X) →
    ∀ A W Y : Subgroup G, Nat.card A = 3 → Subgroup.normalizer (A : Set G) ≤ W → Y ≤ W →
      A ≤ Y → IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) → W ≠ ⊤ →
      ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ → S ≤ W →
        Subgroup.normalizer (S : Set G) ≤ W

@[expose] def KFactL32SimpleNormalizerAll : Prop :=
  ∀ (K : Type) [Group K] [Finite K], F1For K

@[expose] def F1L3Odd : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p ≠ 2 → q.card % 3 = 2 → d.1 = .A 2 q →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → F1For K

@[expose] def F1U3Odd : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p ≠ 2 → q.card % 3 = 1 → d.1 = .twistedA 2 q →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → F1For K

end CFSG.LocalAnalysis.RankThreeUC.S15
