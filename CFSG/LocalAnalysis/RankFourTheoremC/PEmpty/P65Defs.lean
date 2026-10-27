module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane SmallRankSylowTwo smallRankR
  smallRankIsQ8D8)

structure Plane65 {A : Type} [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A)
    (x z : A) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  catalog : CatalogSimpleSections ↥X
  plane : SmallRankPlane p (P : Subgroup A) x z
  sylow_le : (P : Subgroup A) ≤ X
  z_central : z ∈ centralizer ((P : Subgroup A) : Set A)
  four_le : 4 ≤ Open.pRank p (P : Subgroup A)
  rank_centralizer : Open.pRank p (centralizer ({x} : Set A)) ≤ 2
  sylow_centralizer : CFSG.ABGLocalTools.IsSylowOf p
    ((P : Subgroup A) ⊓ centralizer ({x} : Set A)) (centralizer ({x} : Set A))
  perfect : ∀ (N : Subgroup ↥X) [N.Normal], IsPGroup p (↥X ⧸ N) → N = ⊤

@[expose] def KFactP65Single : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A)
    (T : Subgroup A), Plane65 p P X x z →
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X → p = 5 → SmallRankSylowTwo P X T →
    smallRankIsQ8D8 (smallRankR x z T) →
    (∃ L : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p), IsComponentOf L ⊤ ∧
      p ∣ Nat.card L ∧ ∀ K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p),
        IsComponentOf K ⊤ → p ∣ Nat.card K → K = L) →
    ∀ W : Subgroup A, W ≤ X → Nat.Coprime p (Nat.card W) →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set A) → W ≤ rankThreePrimeCore p X

@[expose] def KFactP65Multi : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A),
    Plane65 p P X x z →
    (∃ L K : Subgroup (↥X ⧸ primeComplementCore (G := ↥X) p),
      IsComponentOf L ⊤ ∧ p ∣ Nat.card L ∧ IsComponentOf K ⊤ ∧ p ∣ Nat.card K ∧ L ≠ K) →
    (∀ (f : ℕ) (F : Subgroup A), f.Prime → f ≠ p →
      IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X F →
        Open.pRank p (P : Subgroup A) ≤ Open.pRank p (X ⊓ normalizer (F : Set A))) ∧
    ∀ E : Subgroup A, E ≤ X → IsElemAbelian p E → Nat.card E = p ^ p →
      ∃ a ∈ E, a ≠ 1 ∧ ∃ b ∈ E, b ≠ 1 ∧
        ∀ g ∈ X ⊓ normalizer (E : Set A), g * a * g⁻¹ ∉ zpowers b

@[expose] def KFactP65RankThree : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (X Y Q B : Subgroup A) (x : A),
    p.Prime → 5 ≤ p → CatalogSimpleSections ↥X → Y ≤ X → ¬ X ≤ Y →
    Q ≤ X → IsPGroup p Q → ¬ p ∣ (Q.subgroupOf X).index → 3 ≤ Open.pRank p Q → Q ≤ Y →
    B ≤ Q → IsElemAbelian p B → Nat.card B = p ^ 2 → x ∈ B → x ≠ 1 →
    (∀ y ∈ centralizer (B : Set A), y ^ p = 1 → y ∈ B) →
    Open.pRank p (centralizer ({x} : Set A) ⊓ X) ≤ 2 →
    (∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) →
    (∀ E : Subgroup A, E ≤ Q → IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ S : Subgroup A, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) →
    (∃ N : Subgroup A, N ≤ X ∧ (N.subgroupOf X).Normal ∧ (N.subgroupOf X).index = p) ∧
    (∀ W : Subgroup A, W ≤ X → B ≤ normalizer (W : Set A) →
      Nat.Coprime (Nat.card W) (2 * p) → W ≤ rankThreePrimeCore p X) ∧
    ∃ Q₀ : Subgroup A, Q₀ ≤ Q ∧ IsElemAbelian p Q₀ ∧ Nat.card Q₀ = p ^ p ∧
      ∀ a ∈ Q₀, a ≠ 1 → ∀ b ∈ Q₀, b ≠ 1 →
        ∃ g ∈ X ⊓ normalizer (Q₀ : Set A), g * a * g⁻¹ ∈ zpowers b

@[expose] def KFactP65RankTwo : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (X Q B U : Subgroup A),
    p.Prime → 5 ≤ p → CatalogSimpleSections ↥X → Open.pRank p X = 2 →
    Q ≤ X → IsPGroup p Q → ¬ p ∣ (Q.subgroupOf X).index → IsCyclic (center Q) →
    B ≤ Q → IsElemAbelian p B → Nat.card B = p ^ 2 →
    U ≤ Q → IsElemAbelian p U → Nat.card U = p ^ 2 →
    (∀ g ∈ X, B.map (MulAut.conj g).toMonoidHom ≠ U) →
    (∀ w ∈ Q, orderOf w = p → (∀ q ∈ Q, q * w = w * q) →
      ∀ g ∈ X, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w) →
    (∃ Y : Subgroup A, Y ≤ X ∧ Y ≠ X ∧
      (∀ S : Subgroup A, S ≤ U → 1 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) ∧
      (∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y)) →
    ∀ W : Subgroup A, W ≤ X → B ⊔ U ≤ normalizer (W : Set A) →
      Nat.Coprime (Nat.card W) (2 * p) → W ≤ rankThreePrimeCore p X

@[expose] def KFactP65Rank4 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) (P : Sylow p A) (X : Subgroup A) (x z : A)
    (T : Subgroup A) (f : ℕ) (Fs R : Subgroup A), Plane65 p P X x z →
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X → p = 5 → SmallRankSylowTwo P X T →
    smallRankIsQ8D8 (smallRankR x z T) → f.Prime → f ≠ 2 → f ≠ p →
    IsMaxFInvariantIn f (zpowers x ⊔ zpowers z) X Fs →
    zpowers x ⊔ zpowers z ≤ R → R ≤ X ⊓ normalizer (Fs : Set A) → IsPGroup p R →
    ¬ p ∣ (R.subgroupOf (X ⊓ normalizer (Fs : Set A))).index → 4 ≤ Open.pRank p R →
    IsCyclic (R ⊓ centralizer (Fs : Set A) : Subgroup A) → 4 ≤ Open.pRank f X

@[expose] def P65CoprimeRankTwo : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p f : ℕ) (Y B : Subgroup A), p.Prime → 5 ≤ p → f.Prime →
    f ≠ 2 → f < p → IsPGroup f Y → IsPGroup p B → B ≤ normalizer (Y : Set A) →
    Open.pRank f Y ≤ 2 → B ≤ centralizer (Y : Set A)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
