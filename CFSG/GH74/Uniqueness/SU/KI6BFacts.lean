module

public import CFSG.GH74.Uniqueness.SU.KInputs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup

@[expose] def RankOneFacts : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → CFSG.pRank 2 K ≤ 1 →
    IsPGroup 2 ↥(center K) →
    ∃ z : K, orderOf z = 2 ∧ (∀ y : K, orderOf y = 2 → y = z) ∧ center K = zpowers z ∧
      (∃ y : K, orderOf y = 4) ∧ IsSimpleGroup (K ⧸ center K) ∧
      CFSG.GorensteinWalter.HasDihedralSylowTwo (K ⧸ center K)

@[expose] def NoOuterFourGroup : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K : Subgroup H), K.Normal → CFSG.IsQuasisimple ↥K →
    CFSG.pRank 2 ↥K ≤ 1 → IsPGroup 2 ↥(center ↥K) → centralizer (K : Set H) ≤ K →
    ∀ U : Subgroup H, Nat.card U = 4 → (∀ u ∈ U, u * u = 1) → U ⊓ K ≠ ⊥

@[expose] def RankOneStronglyEmbedded : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → CFSG.pRank 2 K ≤ 1 →
    IsPGroup 2 ↥(center K) → ∀ (S : Sylow 2 K) (D : Subgroup K),
      (S : Subgroup K) ≤ D → D ≠ ⊤ →
      (∀ W : Subgroup K, W ≤ (S : Subgroup K) → 4 ≤ Nat.card W → normalizer (W : Set K) ≤ D) →
      Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 5))

@[expose] def RankOneSL25 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → CFSG.pRank 2 K ≤ 1 →
    IsPGroup 2 ↥(center K) → Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 5)) → IsSL25 K

@[expose] def A5CoverGeneration : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → CFSG.pRank 2 K ≤ 1 →
    IsPGroup 2 ↥(center K) → Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 5)) →
    ∀ (S : Sylow 2 K) (β : MulAut K), β * β = 1 → (∀ k : K, ∃ x : K, β x ≠ k * x * k⁻¹) →
      ∀ D : Subgroup K, normalizer ((S : Subgroup K) : Set K) ≤ D →
        (∀ x : K, β x * x⁻¹ ∈ center K → x ∈ D) → D = ⊤

@[expose] def A5CoverCentralizer : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → CFSG.pRank 2 K ≤ 1 →
    IsPGroup 2 ↥(center K) → Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 5)) →
    ∀ S : Sylow 2 K, centralizer ((S : Subgroup K) : Set K) ≤ center K

structure KI6BFacts : Prop where
  rankOne : RankOneFacts
  noOuter : NoOuterFourGroup
  stronglyEmbedded : RankOneStronglyEmbedded
  sl25 : RankOneSL25
  generation : A5CoverGeneration
  centralizer : A5CoverCentralizer

end CFSG.GH74.Uniqueness.SU.K.R6
