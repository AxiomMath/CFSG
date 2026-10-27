module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactBlockSylowThreeExp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → NineThreeConclusion M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      Nat.Coprime 3 (Nat.card Y)) →
    ∀ Q : Sylow 3 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)),
      IsCyclic (Q : Subgroup ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L))) →
      Nat.card (Q : Subgroup ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L))) ≤ 3

@[expose] def D1OneLieZZbBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ → d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧ L ≠ K) →
    p ^ 2 ∣ Nat.card (R ⊓ d1PlusCore p H K : Subgroup G) →
    ∀ z : G, z ∈ R → z ∈ d1PlusCore p H K → orderOf z = p →
      z ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LiftX p H R K)⁆ →
    ∀ L : Subgroup G, IsTwoPrimeComponent M L → z ∈ L →
      H ⊓ M ≤ Subgroup.normalizer (L : Set G) →
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L ≤ d1PlusCore p H K →
      (∃ m ∈ M, IsWeakSBlock M (pCoreOf 2 H) (L.map (MulAut.conj m).toMonoidHom)) →
    ∀ T : Subgroup G, T ≤ d1PlusCore p H K → IsPGroup 2 T →
      ¬ 2 ∣ (T.subgroupOf (d1PlusCore p H K)).index →
    ∀ H₁ : Subgroup G, GLBIsMaxTwoLocal H₁ → H₁ ≠ H → nclIn H (d1LiftX p H R K) ≤ H₁ →
      pCoreOf 2 M ≤ H₁ → R ⊓ Subgroup.normalizer (T : Set G) ≤ H₁ →
      (∀ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ → nclIn H (d1LiftX p H R K) ≤ H₂ →
        pCoreOf 2 M ≤ H₂ → R ⊓ Subgroup.normalizer (T : Set G) ≤ H₂ →
        Nat.card (nclIn H₂ (d1LiftX p H R K)) ≤ Nat.card (nclIn H₁ (d1LiftX p H R K))) →
      False

end CFSG.AGLEmbedding
