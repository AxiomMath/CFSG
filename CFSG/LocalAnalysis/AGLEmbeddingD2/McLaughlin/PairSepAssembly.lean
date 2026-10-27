module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def PairOneImageRankData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    (∃ x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), x ≠ 1 ∧
      3 ≤ Open.pRank 3 (L ⊓ Subgroup.centralizer ({x} : Set G))) ∨
    ((∀ u ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      IsPGroup 3 (Subgroup.zpowers u) →
        u ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
    ((¬ 3 ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) ∧
      (∀ y ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), y ≠ 1 →
        Open.pRank 3 L ≤ Open.pRank 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) + 1) ∧
      (∀ f : ↥M, (f : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) →
        IsPGroup 3 (Subgroup.zpowers (f : G)) →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) f ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ∀ v ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H),
          (f : G) * v * (f : G)⁻¹ * v⁻¹ ∈ Subgroup.centralizer (L : Set G))) ∨
     (3 ∣ Nat.card (barM M L ⊓
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) ∧
      (∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        E ≤ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        IsElemAbelian 3 E →
        Open.pRank 3 E ≤ Open.pRank 3 (E ⊓
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) + 2) ∧
      ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))))

@[expose] def PairBlockCentreThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

end CFSG.AGLEmbeddingD2.McLaughlin
