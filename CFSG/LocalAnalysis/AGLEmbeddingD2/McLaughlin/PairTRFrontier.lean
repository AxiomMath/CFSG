module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TightCensus
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def PairEvenIndex {G : Type} [Group G] (M H : Subgroup G) : Prop :=
  2 ∣ (H ⊓ M).relIndex H

@[expose] def PairOddIndexResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → ¬ PairEvenIndex M H → False

@[expose] def IsA6OrU33 (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨ IsUThreeThree Y

@[expose] def PairTwoImageTR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L₁ L₂ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ → IsWeakSBlock M (pCoreOf 2 H) L₂ →
    barM M L₁ ≠ barM M L₂ →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      barM M L' = barM M L₁ ∨ barM M L' = barM M L₂) →
    ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ 3 ∣ Nat.card (barM M L₂ ⊓
      Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    IsA6OrU33 ↥(barM M L₁) ∧ IsA6OrU33 ↥(barM M L₂)

@[expose] def PairOneImagePureE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    ∃ x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), x ≠ 1 ∧
      3 ≤ Open.pRank 3 (Subgroup.centralizer ({x} : Set G) ⊓ M)

@[expose] def PairOneImageFixE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → PairEvenIndex M H →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) →
    ∀ y ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), y ≠ 1 →
      3 ∣ Nat.card (M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G)

end CFSG.AGLEmbeddingD2.McLaughlin
