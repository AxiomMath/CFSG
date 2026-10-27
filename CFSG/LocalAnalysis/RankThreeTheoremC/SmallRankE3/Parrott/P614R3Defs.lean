module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LieType.ChevTwo.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo pElementSubgroup)
open CFSG.QuasithinUnique.Setup.Family (GL32)
open scoped MatrixGroups

@[expose] def KFactChevTwoRankOneThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsChevTwo K → CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1 →
    ¬ CFSG.Open.fusionIsBenderGroup K →
      ∃ n : ℕ, Odd n ∧ Nonempty (K ≃* PSL(3, GaloisField 2 n))

@[expose] def KFact135Three : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsChevTwo K → CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1 →
    ∀ R : Subgroup K, IsPGroup 2 R → R ≠ ⊥ →
      pCoreOf 2 (normalizer (R : Set K)) = R →
      ∃ T : Subgroup K, T ≤ normalizer (R : Set K) ∧ IsPGroup 2 T ∧ ¬ 2 ∣ T.index

@[expose] def KFactTwoInvolutionsThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsChevTwo K → CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1 →
    ∀ R : Subgroup (MulAut K), IsPGroup 2 R → ¬ IsCyclic R →
      R ⊓ (MulAut.conj : K →* MulAut K).range = ⊥ →
      ∃ s₁ ∈ R, ∃ s₂ ∈ R, orderOf s₁ = 2 ∧ orderOf s₂ = 2 ∧
        Subgroup.closure ({g : K | s₁ g = g} ∪ {g : K | s₂ g = g}) = ⊤

@[expose] def KFact136Three : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsChevTwo K → CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1 →
    ∀ R : Subgroup K, IsPGroup 2 R → R ≠ ⊥ → 2 ∣ R.index →
      pCoreOf 2 (normalizer (R : Set K)) = R →
      3 ∣ Nat.card (pElementSubgroup 2 (normalizer (R : Set K))) →
      Nonempty (K ≃* GL32) ∨
        ∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ f ≠ 3 ∧
          f ∣ Nat.card (CFSG.pLayer ↥(normalizer (R : Set K)) 3) ∧
          2 ≤ CFSG.Open.pRank f (⊤ : Subgroup K)

@[expose] def Piece619Three : Prop :=
  KFactBenderGen → KFactBenderTI → CFSG.AGLEmbedding.AschbacherLocalCGTBlock → KFact135Three →
    CFSG.LieType.ChevTwo.Chev2KDOut → KFactTwoInvolutionsThree → KFactTransvRankOne →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S K : Subgroup G), Hyp P M x z H S → Stage618 M H K z →
      A5Case H S K ∨ LieCase M H S K x z

@[expose] def Piece620Three : Prop :=
  KFact136Three → KFactOutThreePrimeSimple →
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) (x z : G)
    (H S K : Subgroup G), Hyp P M x z H S → Stage618 M H K z →
      A5Case H S K ∨ LieCase M H S K x z → ∃ b : G, Stage620 H S K x z b

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
