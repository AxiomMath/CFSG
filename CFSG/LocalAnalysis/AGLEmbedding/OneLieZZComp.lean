module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockInvertedThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    ∃ a ∈ Subgroup.normalizer (S : Set G) ⊓ L, ∃ g ∈ Subgroup.normalizer (S : Set G) ⊓ L,
      orderOf a = 3 ∧ g * a * g⁻¹ * a ∈ pCoreOf 2 M

@[expose] def KFactBlockCenterCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ barM M L →
      A ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup p A →
      IsCyclic A

@[expose] def D1OneLieZZComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
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
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ →
    ∀ L : Subgroup G, IsTwoPrimeComponent M L → z ∈ L →
      H ⊓ M ≤ Subgroup.normalizer (L : Set G) →
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ d1PlusCore p H K →
      (∃ m ∈ M, IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj m).toMonoidHom)) → False

end CFSG.AGLEmbedding
