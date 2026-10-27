module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedStructure
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LocalAnalysis.RankThreeTheoremC

structure GNLocal {X : Type} [Group X] [Finite X] (T : Subgroup X) : Prop where
  solv : ∀ C : Subgroup X, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.normalizer (C : Set X))
  e9 : ∀ C : Subgroup X, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
    ∀ U : Subgroup X, U ≤ Subgroup.normalizer (C : Set X) → IsPGroup 3 U → ¬ IsCyclic U →
      IsElemAbelian 3 U ∧ Nat.card U = 9 ∧
        TransitiveOnNonidentity (Subgroup.normalizer (U : Set X)) U

@[expose] def ThreePrimeJCentral : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ N : Subgroup (X ⧸ gnC T), N.Normal → Nat.Coprime 3 (Nat.card N) →
      ⁅N, gnImg T (thompsonJ T)⁆ = ⊥

@[expose] def AGL81I56 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ = L →
      ∀ n : ℕ, 8 < n → Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)) →
        ¬ CFSG.HallHigman.IsPSolvable 3
          ↥(gnImg T (Subgroup.centralizer (omegaOneCenterOf T : Set X)) ⊓ L)

@[expose] def KFactParabolicCoverRankTwo : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (L S₀ A₁ A₂ : Subgroup W), IsComponentOf L ⊤ →
    IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) → IsSylowTwoOf S₀ L →
    CoveredByTwo L S₀ A₁ A₂ → CFSG.HallHigman.IsPSolvable 3 ↥A₁ →
    CFSG.HallHigman.IsPSolvable 3 ↥A₂ →
    (∀ E : Subgroup W, (E ≤ A₁ ⊓ L ∨ E ≤ A₂ ⊓ L) → IsPGroup 3 E → ¬ IsCyclic E →
      IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
        TransitiveOnNonidentity (Subgroup.normalizer (E : Set W)) E) →
    IsRankTwoLayerType (↥L ⧸ Subgroup.center ↥L)

@[expose] def KFactAltSevenE9 : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (L E N : Subgroup W), IsComponentOf L ⊤ →
    Nonempty (↥L ≃* alternatingGroup (Fin 7)) → E ≤ L → IsElemAbelian 3 E → Nat.card E = 9 →
    N ≤ Subgroup.normalizer (L : Set W) → N ≤ Subgroup.normalizer (E : Set W) →
    ¬ TransitiveOnNonidentity N E

@[expose] def KFactOddCentreE9 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    ¬ 2 ∣ Nat.card (Subgroup.center Y) →
    (IsRankTwoLayerType (Y ⧸ Subgroup.center Y) ∨
      Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 7))) →
      Subgroup.center Y = ⊥ ∨
        (Nat.card (Subgroup.center Y) = 3 ∧
          (∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E = 9 → Subgroup.center Y ≤ E) ∧
          ∀ y : Y, orderOf y ≠ 9)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
