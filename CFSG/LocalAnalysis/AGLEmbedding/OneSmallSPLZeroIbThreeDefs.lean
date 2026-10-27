module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactSPLInvolveScalar : Prop :=
  ∀ (KC : Type) [Group KC] [Finite KC], IsSimpleGroup KC → (∃ a b : KC, a * b ≠ b * a) →
    IsCatalogGroup KC → ∀ T : Sylow 3 KC, ¬ IsCyclic (T : Subgroup KC) →
    GLBCore 3 1 (T : Subgroup KC) ≠ ⊤ → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut KC)) →
    ∀ (W : Subgroup KC) (L : Type) [Group L] [Finite L], IsSPLFamily 3 L →
    ∀ f : W →* L, Function.Surjective f → (∀ w : W, f w = 1 → Nat.Coprime 3 (orderOf w)) →
    ∀ E : Subgroup KC, E ≤ W → IsPGroup 3 E →
    (∃ TL : Sylow 3 L, (E.subgroupOf W).map f = (TL : Subgroup L)) →
    ∀ T' : Sylow 3 KC, E ≤ T' →
    ∃ A : Subgroup KC, A ≤ T' ∧ IsElemAbelian 3 A ∧
      E ⊓ Subgroup.centralizer (E : Set KC) ≤ A ∧
      ∃ c ∈ Subgroup.normalizer (A : Set KC), ∃ m lam : ℕ, 5 ≤ 2 * m ∧ ¬ 3 ∣ lam - 1 ∧
        (∀ a ∈ A, c ^ m * a * (c ^ m)⁻¹ = a ^ lam) ∧
        ∀ k, 0 < k → k < m → ∀ F : Subgroup KC, F ≤ A → F.relIndex A = 3 →
          c ^ k ∉ Subgroup.normalizer (F : Set KC)

@[expose] def D1SmallSPLZeroIbThreeComps : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D1OneSmallData 3 P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX 3 H R K)) → ∀ z : G, D1SmallCZElt 3 H R K z →
    IsSPLFamily 3 K → D1CzSP 3 z → D1CzOutside 3 z → d1MapPCore 3 M H = ⊥ →
    ¬ D1SmallIa 3 H K → CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ →
    (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      d1LiftX 3 H R K ≤ Subgroup.normalizer (L : Set G)) →
    ∀ L : Subgroup G, IsTwoPrimeComponent M L →
      (IsWeakSBlock M (pCoreOf 2 H) L ∨ L ≤ GLBPrimeCore 3 H) →
      barM M (d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G)) ≤
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def D1SmallSPLZeroIbThreeBlocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D1OneSmallData 3 P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX 3 H R K)) → ∀ z : G, D1SmallCZElt 3 H R K z →
    IsSPLFamily 3 K → D1CzSP 3 z → D1CzOutside 3 z → d1MapPCore 3 M H = ⊥ →
    ¬ D1SmallIa 3 H K → CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ →
    (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      d1LiftX 3 H R K ≤ Subgroup.normalizer (L : Set G)) →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M (d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G)) ≤
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def BlockThreeIbHyp {G : Type} [Group G] [Finite G] (M S L : Subgroup G)
    (D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (x : ↥M ⧸ CFSG.pCore 2 ↥M) : Prop :=
  CFSG.Open.IsKGroup ↥M ∧ Asc81bHyp M S ∧ IsWeakSBlock M S L ∧ NineThreeConclusion M S L ∧
    ¬ InClassXBlock L ∧ Nat.Coprime 3 (Nat.card (Subgroup.center ↥(barM M L))) ∧
    CFSG.Open.pRank 3 (blockPL M S L) ≤ 3 ∧
    (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ V → IsPGroup 3 A → IsCyclic A) ∧
    ⁅D, D⁆ = D ∧
    D ≤ blockPL M S L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
    (∀ A : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), A ≤ D → IsPGroup 3 A → IsCyclic A) ∧
    (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M S L → ⁅V, V⁆ = V →
      ∀ k : ℕ, 3 ^ k ∣ Nat.card V → 3 ^ k ∣ Nat.card D) ∧
    x ∈ D ∧ x ^ 3 = 1 ∧ x ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
    ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ barM M L → ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({x} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → W = ⊥

@[expose] def KFactBlockCentRankIbThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (x : ↥M ⧸ CFSG.pCore 2 ↥M), BlockThreeIbHyp M S L D x →
    ∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      E ≤ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      E ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsElemAbelian 3 E →
      Nat.card E = 3 ^ 2 →
      ∀ t ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      t ∈ Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      (∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ E → Nat.card F = 3 →
        t ∉ Subgroup.normalizer (F : Set (↥M ⧸ CFSG.pCore 2 ↥M))) →
      E ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≠ ⊥

@[expose] def KFactBlockCentAbThreeIb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (x : ↥M ⧸ CFSG.pCore 2 ↥M), BlockThreeIbHyp M S L D x →
    ∀ U : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      U ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      U ≤ Subgroup.normalizer (blockPL M S L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      U ≤ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsPGroup 3 U →
      ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈
        Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def KFactBlockCenterThreeIb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G) (D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))
    (x : ↥M ⧸ CFSG.pCore 2 ↥M), BlockThreeIbHyp M S L D x →
    ∀ y ∈ barM M L, y ^ 3 = 1 → y ∈ Subgroup.centralizer (D : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      y ∈ D ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      y ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

end CFSG.AGLEmbedding
