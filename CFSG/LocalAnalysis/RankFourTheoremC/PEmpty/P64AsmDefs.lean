module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.Blueprint Subgroup
open scoped MatrixGroups

@[expose] def P64IsI246Type (p : ℕ) (S : Type) [Group S] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), p ∣ Nat.card K - 1 ∧
      Nonempty (S ≃* StatedProj (StatedSL p K))) ∨
    (∃ (q : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧ p ∣ q + 1 ∧
      Nonempty (S ≃* StatedProj (StatedSU p q K))) ∨
    (p = 5 ∧ NativeSporadic.IsSporadic S .Co1) ∨
    StatedClassicalModel S .PSp 2 p 1 ∨ ChevalleyExceptionalModel S .G2 p 1

@[expose] def P64IsL2pp (p : ℕ) (L : Type) [Group L] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ p ∧
    Nonempty (L ≃* PSL(2, K))

@[expose] def P64IsU3p (p : ℕ) (L : Type) [Group L] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ 2 ∧
    Nonempty (L ≃* StatedProj (StatedSU 3 p K))

@[expose] def KDL64I291 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z], CatalogSimpleSections Z →
    primeComplementCore (G := Z) p = ⊥ →
    ∀ L : Subgroup Z, IsComponentOf L ⊤ → (∀ K : Subgroup Z, IsComponentOf K ⊤ → K = L) →
      3 ≤ Open.pRank p (⊤ : Subgroup Z) → ∀ x : Z, orderOf x = p →
        Open.pRank p (centralizer ({x} : Set Z)) = 2 →
        (∀ y ∈ CFSG.pCore p Z, y ^ p = 1 → y ∈ L) ∧
          (P64IsI246Type p (↥L ⧸ center ↥L) ∨
            (P64IsL2pp p ↥L ∧ ∃ N : Subgroup Z, N.Normal ∧ N.index = p))

@[expose] def KDL64TypeRank : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L →
    P64IsI246Type p (L ⧸ center L) → ∀ P : Sylow p L, 3 ≤ Open.pRank p (P : Subgroup L)

@[expose] def KDL64I246 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z], CatalogSimpleSections Z →
    primeComplementCore (G := Z) p = ⊥ →
    ∀ L : Subgroup Z, IsComponentOf L ⊤ → P64IsI246Type p (↥L ⧸ center ↥L) →
      ∀ P : Subgroup Z, P ≤ L → IsPGroup p P → ¬ p ∣ (P.subgroupOf L).index →
        3 ≤ Open.pRank p P →
        ∀ Y : Subgroup Z,
          (∀ S : Subgroup Z, S ≤ P → 2 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) →
          (∀ E : Subgroup Z, E ≤ P → IsElemAbelian p E → Nat.card E = p ^ 3 →
            ∀ S : Subgroup Z, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set Z) ≤ Y) → L ≤ Y

@[expose] def KDL64I204L2 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z] (L : Subgroup Z), L.Normal →
    P64IsL2pp p ↥L → centralizer (L : Set Z) = ⊥ →
    ∀ B : Subgroup Z, IsElemAbelian p B → Nat.card B = p ^ 2 →
      (∀ y ∈ centralizer (B : Set Z), y ^ p = 1 → y ∈ B) →
      ∀ W : Subgroup Z, B ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) → W = ⊥

@[expose] def KDL64I204U3 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Z : Type) [Group Z] [Finite Z] (L : Subgroup Z), L.Normal →
    P64IsU3p p ↥L → centralizer (L : Set Z) = ⊥ →
    ∀ B : Subgroup Z, IsElemAbelian p B → Nat.card B = p ^ 2 →
      (∀ y ∈ centralizer (B : Set Z), y ^ p = 1 → y ∈ B) →
      ∀ W : Subgroup Z, B ≤ normalizer (W : Set Z) → Nat.Coprime (Nat.card W) (2 * p) → W = ⊥

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
