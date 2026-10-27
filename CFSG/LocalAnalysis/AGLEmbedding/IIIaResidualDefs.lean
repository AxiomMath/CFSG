module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Package

variable {G : Type} [Group G] [Finite G]

structure D1L2Data (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Sylow p G) (M H R X : Subgroup G) :
    Prop where
  ph3 : D1PhaseThree p P M H R
  ind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q
  three_le : 3 ≤ n
  le_R : X ≤ R
  torus : ∃ φ : Multiplicative (GaloisField p n) ≃* X, ∀ μ : (GaloisField p n)ˣ,
    ∃ t ∈ H ⊓ M, ∀ a : Multiplicative (GaloisField p n),
      t * (φ a : G) * t⁻¹ =
        φ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a))
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  pcore_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    (∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ GLBPrimeCore p H) → Y ≤ X ⊔ GLBPrimeCore p H
  pRank_le : Open.pRank p (H ⊓ M) ≤ n
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H

end Package

section Blocks

variable {G : Type} [Group G]

@[expose] def BlockHasThree (M S L : Subgroup G) : Prop :=
  ∃ y ∈ Subgroup.normalizer (S : Set G) ⊓ L, IsPGroup 3 (Subgroup.zpowers y) ∧
    ∃ l ∈ L, y * l * y⁻¹ * l⁻¹ ∉ pCoreOf 2 M

@[expose] def blockClosure (M K L : Subgroup G) : Subgroup G :=
  pCoreOf 2 M ⊔ ⨆ (k : G) (_ : k ∈ K), L.map (MulAut.conj k).toMonoidHom

end Blocks

@[expose] def KFactL2AutElemRank : Prop :=
  ∀ (p n : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ n → ∀ E : Subgroup (MulAut (PSL2GF p n)),
    IsElemAbelian p E → Nat.card E ≤ p ^ n

@[expose] def KFactParabolicThree : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y,
    IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
      J ≠ Subgroup.normalizer (T : Set Y) → 3 ∣ Nat.card J

@[expose] def CitedBlockThreeTransvection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → BlockHasThree M S L

@[expose] def KFactBlockThreeAltSeven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L → NineThreeFive M L →
    BlockHasThree M S L

@[expose] def StmtLemmaB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L X : Subgroup G) (p r : ℕ) (t : G),
    Open.IsKGroup ↥M → Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L →
    ¬ IsSylowTwoOf (S ⊓ L) L → p.Prime → p ≠ 2 →
    (∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (S : Set G) → ⁅Y, Y⁆ = Y →
      p.Coprime (Nat.card Y)) →
    X ≤ M ⊓ Subgroup.normalizer (S : Set G) → X ≤ Subgroup.normalizer (L : Set G) →
    IsElemAbelian p X → p ^ 3 ≤ Nat.card X →
    t ∈ M ⊓ Subgroup.normalizer (S : Set G) → t ∈ Subgroup.normalizer (L : Set G) →
    t ∈ Subgroup.normalizer (X : Set G) →
    r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p → ¬ r ∣ p - 1 →
    (∀ x ∈ X, t ^ r * x * (t ^ r)⁻¹ = x) → (∃ x ∈ X, t * x * t⁻¹ ≠ x) →
    (∀ Y : Subgroup G, Y ≤ X → t ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X) →
    barM M X ≤ Subgroup.centralizer (barM M L : Set _)

@[expose] def KFactThreeOrFiveDvd : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
    IsCatalogGroup Y → 3 ∣ Nat.card Y ∨ 5 ∣ Nat.card Y

@[expose] def KFactOutElemRank : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L E : Subgroup Y), IsComponentOf L ⊤ →
    IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card L →
    E ≤ Subgroup.normalizer (L : Set Y) → IsElemAbelian p E →
    E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ → Nat.card E ≤ p

@[expose] def StmtL2Data : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ∀ (n : ℕ) (d : TauCeti.ValidLieTypeIndex), IsLinTwoIndex p n d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        D1L2Data p n P M H R (d1LiftX p H R K)

@[expose] def StmtPPDElement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X →
    ∃ (r : ℕ) (t : G), r.Prime ∧ n < r ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ p ∧ ¬ r ∣ p - 1 ∧
      t ∈ H ⊓ M ∧ t ∈ Subgroup.normalizer (X : Set G) ∧ IsPGroup r (Subgroup.zpowers t) ∧
      (∀ x ∈ X, t ^ r * x * (t ^ r)⁻¹ = x) ∧ (∃ x ∈ X, t * x * t⁻¹ ≠ x) ∧
      ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ X →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X

@[expose] def StmtBlockThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G},
    D1PhaseThree p P M H R → IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L

@[expose] def StmtXNormalizesBlockThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → p = 3 → ∀ L : Subgroup G,
      IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L →
      X ≤ Subgroup.normalizer (L : Set G)

@[expose] def StmtNormalizeBlocks : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → (p = 3 ∨ 5 ≤ p) →
    (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L) →
    ∀ (r : ℕ) (t : G), r.Prime → n < r → 5 ≤ r → t ∈ H ⊓ M → IsPGroup r (Subgroup.zpowers t) →
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        X ≤ Subgroup.normalizer (L : Set G) ∧ t ∈ Subgroup.normalizer (L : Set G)

@[expose] def StmtROne : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → (p = 3 ∨ 5 ≤ p) →
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        barM M X ≤ Subgroup.centralizer (barM M L : Set _)

@[expose] def StmtLePCoreThree : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → p = 3 →
      barM M X ≤ CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M)

@[expose] def StmtP3OfData : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → p = 3 →
      ((X ⊔ pCoreOf 2 M).subgroupOf M).Normal

@[expose] def StmtFiveKComponents : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → 5 ≤ p →
      ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ H ⊓ M →
        barM M X ≤ Subgroup.centralizer (barM M L : Set _)

@[expose] def StmtFiveComponents : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → 5 ≤ p →
      ∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
        barM M X ≤ Subgroup.centralizer (Lbar : Set _)

@[expose] def StmtFiveOddCore : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → 5 ≤ p →
      ∀ s : ℕ, s.Prime → s ≠ 2 → s < p →
        barM M X ≤ Subgroup.centralizer ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) :
          Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)

@[expose] def StmtFiveReduce : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p n : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R X : Subgroup G}, D1L2Data p n P M H R X → 5 ≤ p →
      (∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
        barM M X ≤ Subgroup.centralizer (Lbar : Set _)) ∧
      ∀ s : ℕ, s.Prime → s ≠ 2 → s < p →
        barM M X ≤ Subgroup.centralizer ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) :
          Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _)

end CFSG.AGLEmbedding
