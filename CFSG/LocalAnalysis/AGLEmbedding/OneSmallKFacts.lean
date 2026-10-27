module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

@[expose] def KFactSmallAutRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (T : Subgroup K) ≤ 2 → Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

structure OneSmallFacts (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) : Prop where
  pSubgroup_le : ∀ Y : Subgroup (MulAut K), IsPGroup p Y →
    Y ≤ Subgroup.normalizer (((T : Subgroup K).map (MulAut.conj : K →* MulAut K) :
      Subgroup (MulAut K)) : Set (MulAut K)) →
    (Subgroup.normalizer ((T : Subgroup K) : Set K)).map (MulAut.conj : K →* MulAut K) ≤
      Subgroup.normalizer (Y : Set (MulAut K)) →
    Y ≤ (T : Subgroup K).map (MulAut.conj : K →* MulAut K)
  torus : ∃ T₀ : Subgroup K, T₀ ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧
    p.Coprime (Nat.card T₀) ∧ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥
  centralizer : ∀ V : Subgroup K, V ≤ T → V ≠ ⊥ →
    Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
    (∀ f : MulAut K, (∀ v ∈ V, f v = v) → ∃ t ∈ (T : Subgroup K), f = MulAut.conj t) ∨
      (V = centerOf (T : Subgroup K) ∧ centerOf (T : Subgroup K) ≠ T)

@[expose] def KFactUPrimeSmall : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → ¬ (p = 3 ∧ IsLinThreeFour K) →
      ¬ (p = 5 ∧ IsFi22 K) → KFactUPrime p K

@[expose] def KFactUPrimeExc : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), (p = 3 ∧ IsLinThreeFour K) ∨ (p = 5 ∧ IsFi22 K) →
    ∀ T : Sylow p K, GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      (∀ Y : Subgroup K, GLBCore p 1 (T : Subgroup K) ≤ Y →
        Y = GLBCore p 1 (T : Subgroup K) ∨ Y = ⊤) ∧
      ∀ N : Subgroup K, N ≤ GLBCore p 1 (T : Subgroup K) →
        (N.subgroupOf (GLBCore p 1 (T : Subgroup K))).Normal → p.Coprime (Nat.card N) → N = ⊥

@[expose] def KFactOneSmall : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → ¬ (p = 3 ∧ IsLinThreeFour K) →
      ¬ (p = 5 ∧ IsFi22 K) → OneSmallFacts p K T

@[expose] def KFactL34Local : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsLinThreeFour K → ∀ T : Sylow 3 K,
    (∃ T₀ : Subgroup K, T₀ ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧
      Nat.Coprime 3 (Nat.card T₀) ∧ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥) ∧
    ∀ V : Subgroup K, V ≤ T → V ≠ ⊥ →
      Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
      ∀ f : MulAut K, (∀ v ∈ V, f v = v) →
        ∃ t ∈ (T : Subgroup K), ∀ k ∈ GLBCore 3 1 (T : Subgroup K), f k = t * k * t⁻¹

@[expose] def KFactFi22GuestRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsFi22 K → ∀ T : Sylow 5 K,
    ∃ E : Subgroup K, E ≤ GLBCore 5 1 (T : Subgroup K) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 4

@[expose] def KFactOneLieSmallLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p →
    (IsSmallLinTwo p K ∨ IsSmallUnitary p K) → ∀ T : Sylow p K, OneLieFacts p K T

@[expose] def KFactSmallBorelSolvable : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p.Prime → 5 ≤ p →
    (IsSmallLinTwo p K ∨ IsSmallUnitary p K) → ∀ T : Sylow p K,
      Group.IsSolvable (GLBCore p 1 (T : Subgroup K))

@[expose] def KFactAlphaFive : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) → ∀ p : ℕ, p.Prime → 5 ≤ p →
    Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ∀ T : Sylow p K,
      (KGenThree p K ∧ (3 ≤ Open.pRank p (⊤ : Subgroup K) ∨ KOutNormalSylow p K)) ∨
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∨
      (GLBCore p 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K))

@[expose] def KFactSmallInvolve : Prop :=
  ∀ (KC : Type) [Group KC] [Finite KC], IsSimpleGroup KC → (∃ a b : KC, a * b ≠ b * a) →
    IsCatalogGroup KC → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p KC,
      ¬ IsCyclic (T : Subgroup KC) → GLBCore p 1 (T : Subgroup KC) ≠ ⊤ →
      3 ≤ Open.pRank p (⊤ : Subgroup (MulAut KC)) →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
      IsCatalogGroup L → ∀ TL : Sylow p L, ¬ IsCyclic (TL : Subgroup L) →
      GLBCore p 1 (TL : Subgroup L) ≠ ⊤ → Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2 →
    ∀ (A : Subgroup KC) (f : A →* L), Function.Surjective f → IsSPLFamily p L

end CFSG.AGLEmbedding
