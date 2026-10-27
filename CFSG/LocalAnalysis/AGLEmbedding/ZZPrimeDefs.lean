module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactOneLieBorelSolvable : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      Group.IsSolvable (GLBCore p 1 (T : Subgroup K))

@[expose] def KFactTwoGenInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → 5 ≤ p →
    (¬ p ∣ Nat.card L ∨ IsOrthogonalTwo ↥L ∨
      (∃ m : ℕ, Nonempty (↥L ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin m))) ∨
      (IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) ∧ ∃ T : Subgroup Y, IsSylowTwoOf T L ∧
        p.Coprime (Nat.card ↥(L ⊓ Subgroup.normalizer (T : Set Y))))) →
    ∀ x ∈ Subgroup.closure
        {a : Y | a ∈ Subgroup.normalizer (L : Set Y) ∧ ∃ k : ℕ, a ^ 2 ^ k = 1},
      (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ L ⊔ Subgroup.centralizer (L : Set Y)

@[expose] def KFactParabolicPrime : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Open.IsQuasisimple Y →
    IsClassicalTwoOrG2 (Y ⧸ Subgroup.center Y) → ∀ T J : Subgroup Y, IsSylowTwoOf T ⊤ →
    Subgroup.normalizer (T : Set Y) ≤ J → J ≠ Subgroup.normalizer (T : Set Y) →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
    (∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → p.Coprime (Nat.card U)) → p.Coprime (Nat.card J)

@[expose] def CitedBlockTransvectionPrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → p.Prime → 5 ≤ p →
    (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      ⁅V, V⁆ = V → p.Coprime (Nat.card V)) →
    p.Coprime (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))

@[expose] def KFactBlockAltSevenPrime : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (p : ℕ), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeFive M L → p.Prime → 5 ≤ p →
    (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
      ⁅V, V⁆ = V → p.Coprime (Nat.card V)) →
    p.Coprime (Nat.card (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))

@[expose] def D1OneLieZZ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
    d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) →
    p = 3 →
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ → False

@[expose] def D1OneLieZZb3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧ L ≠ K) →
    d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) →
    p = 3 →
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ → False

@[expose] def D1OneLieZZbHat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧ L ≠ K) →
    d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) →
    5 ≤ p →
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ →
    ∀ L : Subgroup G, IsTwoPrimeComponent M L →
      (∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
        V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ∧ ⁅V, V⁆ = V ∧
          p ∣ Nat.card V) →
      barM M (Subgroup.zpowers z) ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

end CFSG.AGLEmbedding
