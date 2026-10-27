module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.HSStd

@[expose] def KGPumpTableT : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Catalog S → IsSimpleGroup S →
    ∀ τ : MulAut S, τ * τ = 1 → τ ≠ 1 →
    ∀ N : Subgroup S, N ≤ autCentralizer τ → CFSG.IsQuasisimple ↥N →
      (N.subgroupOf (autCentralizer τ)).IsSubnormal → IsPGroup 2 (center ↥N) →
      (Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin 8)) →
          (∃ m : ℕ, 5 ≤ m ∧ Nonempty (S ≃* alternatingGroup (Fin (2 * m)))) ∨ IsSporadic S .HS ∨
            LieModel S .PSL 4 2 2 ∨ (IsSporadic S .McL ∧ Nat.card (center ↥N) = 2)) ∧
      (∀ j : ℕ, 5 ≤ j → Nonempty (↥N ⧸ center ↥N ≃* alternatingGroup (Fin (2 * j))) →
          (∃ m : ℕ, j < m ∧ Nonempty (S ≃* alternatingGroup (Fin (2 * m)))) ∨
            (j = 5 ∧ IsSporadic S .HN)) ∧
      (IsSporadic (↥N ⧸ center ↥N) .HS → IsSporadic S .HN ∧ Nat.card (center ↥N) = 2) ∧
      ¬ IsSporadic (↥N ⧸ center ↥N) .McL ∧ ¬ IsSporadic (↥N ⧸ center ↥N) .HN ∧
      (∀ i : ℕ, 1 ≤ i → LieModel (↥N ⧸ center ↥N) .PSL 4 2 (2 ^ i) →
        LieModel S .PSL 4 2 (2 ^ (i + 1)))

@[expose] def SolomonIAltCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (↥L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2

@[expose] def KGA10A8 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* alternatingGroup (Fin 10)) →
    ∀ A : Subgroup K, Nonempty (↥A ≃* alternatingGroup (Fin 8)) →
      Nat.card {σ : MulAut K // ∀ a ∈ A, σ a = a} ≤ 2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
