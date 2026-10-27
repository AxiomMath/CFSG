module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped MatrixGroups

@[expose] def KFactL2UnipotentCoprime : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ {G : Type} [Group G] [Finite G] (L : Subgroup G),
    Nonempty (L ≃* PSL(2, GaloisField p 2)) → ∀ u ∈ L, orderOf u = p →
      ∀ V : Subgroup G, V ≤ L → ¬ p ∣ Nat.card V → u ∈ normalizer (V : Set G) → V = ⊥

structure Gen49BHyp (p : ℕ) [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    (S R Γ : Subgroup Y) (x : Y) : Prop where
  ne_two : p ≠ 2
  core_eq_bot : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  sylow : IsSylowOf p S ⊤
  abelian : IsMulCommutative S
  le_sylow : R ≤ S
  elemAbelian : IsElemAbelian p R
  card_eq : Nat.card R = p ^ 2
  pRank_le : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2
  mem : x ∈ R
  ne_one : x ≠ 1
  weakClosed : ∀ g : Y, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ S →
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x
  normalizer_S : normalizer (S : Set Y) ≤ Γ
  normalizer_R : normalizer (R : Set Y) ≤ Γ
  others : ∀ a ∈ R, a ≠ 1 → zpowers a ≠ zpowers x →
    centralizer ({a} : Set Y) ≤ Γ ∧ normalizer ((zpowers a : Subgroup Y) : Set Y) ≤ Γ

@[expose] def GL83Generic4_9BNormal : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {S R Γ : Subgroup Y} {x : Y},
    Gen49BHyp p S R Γ x → CFSG.pCore p Y ≠ ⊥ →
      Γ = ⊤ ∨ ∃ K : Subgroup Y, K.Normal ∧ K ≤ centralizer ({x} : Set Y) ∧ ¬ K ≤ Γ

@[expose] def GL83Generic4_9BLayer : Prop :=
  KFactInnerAction → KFactWeakClosure →
  ∀ {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {S R Γ : Subgroup Y} {x : Y},
    Gen49BHyp p S R Γ x → CFSG.pCore p Y = ⊥ →
      Γ = ⊤ ∨ ∃ K : Subgroup Y, K.Normal ∧ K ≤ centralizer ({x} : Set Y) ∧ ¬ K ≤ Γ

@[expose] def GL83Generic4_9B : Prop :=
  KFactInnerAction → KFactWeakClosure →
  ∀ {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {S R Γ : Subgroup Y} {x : Y},
    Gen49BHyp p S R Γ x →
      Γ = ⊤ ∨ ∃ K : Subgroup Y, K.Normal ∧ K ≤ centralizer ({x} : Set Y) ∧ ¬ K ≤ Γ

@[expose] def Gen49Cover (G : Type) [Group G] [Finite G] (p : ℕ) (M : Subgroup G) (x : G)
    (R : Subgroup G) : Prop :=
  ∀ H : Subgroup G, H ≠ ⊤ → R ≤ H → CFSG.Open.pRank p H ≤ 2 → ¬ H ≤ M →
    rankThreePrimeCore p H ≤ M →
    ∃ X : Subgroup G, X ≤ H ∧ rankThreePrimeCore p H ≤ X ∧ (X.subgroupOf H).Normal ∧
      (∀ h ∈ X, h * x * h⁻¹ * x⁻¹ ∈ rankThreePrimeCore p H) ∧ ¬ X ≤ M

end CFSG.LocalAnalysis.RankThreeTheoremC
