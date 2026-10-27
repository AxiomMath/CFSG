module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HSStd

@[expose] def PumpType (Q : Type) [Group Q] : Prop :=
  (∃ k : ℕ, 4 ≤ k ∧ Nonempty (Q ≃* alternatingGroup (Fin (2 * k)))) ∨
    IsSporadic Q .HS ∨ IsSporadic Q .McL ∨ IsSporadic Q .HN ∨
    ∃ i : ℕ, 1 ≤ i ∧ LieModel Q .PSL 4 2 (2 ^ i)

@[expose] def KGPumpTable : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Catalog S → IsSimpleGroup S →
    ∀ τ : MulAut S, τ * τ = 1 → τ ≠ 1 →
    ∀ N : Subgroup S, N ≤ autCentralizer τ → CFSG.IsQuasisimple ↥N →
      (N.subgroupOf (autCentralizer τ)).IsSubnormal → IsPGroup 2 (center ↥N) →
      PumpType (↥N ⧸ center ↥N) →
        PumpType S ∧ ¬ Nonempty (S ≃* alternatingGroup (Fin 8)) ∧
          (IsSporadic S .HS → Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin 8)))

@[expose] def KGPumpRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → IsPGroup 2 (center K) →
    PumpType (K ⧸ center K) → 2 ≤ CFSG.pRank 2 K

@[expose] def KGHSA8 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Catalog K → IsSimpleGroup K → Nat.card K = 44352000 →
    ∀ A : Subgroup K, Nonempty (↥A ≃* alternatingGroup (Fin 8)) →
      Nat.card {σ : MulAut K // ∀ a ∈ A, σ a = a} ≤ 2

@[expose] def Co1InvCentralizers : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSporadic Y .Co1 →
    ∀ y : Y, orderOf y = 2 → Nat.card (centralizer ({y} : Set Y)) ≠ 177408000

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
