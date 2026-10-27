module

public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.InvariantTwoWithin
public import CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreReduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

structure Lemma212Config (p : ℕ) {H : Type*} [Group H] [Finite H] (P : Sylow p H) (z : H)
    (D : Subgroup H) : Prop where
  rank : CFSG.Open.pRank p (P : Subgroup H) = 3
  ord : orderOf z = p
  central : z ∈ centralizer ((P : Subgroup H) : Set H)
  unique : ∀ y ∈ (P : Subgroup H), y ∈ centralizer ((P : Subgroup H) : Set H) → y ^ p = 1 →
    y ∈ zpowers z
  le : D ≤ (P : Subgroup H)
  elem : IsElemAbelian p D
  card : Nat.card D = p ^ 2
  mem : z ∈ D
  notNormal : ¬ (P : Subgroup H) ≤ normalizer (D : Set H)
  sylow : CFSG.ABGLocalTools.IsSylowOf p D (centralizer (D : Set H))

@[expose] def IsPlaneDiagonal (p : ℕ) {H : Type*} [Group H] (D : Subgroup H) (z g : H) : Prop :=
  g ∈ normalizer (D : Set H) ∧ p.Coprime (orderOf g) ∧
    ∃ a b : ℕ, a * b % p = 1 ∧ orderOf (a : ZMod p) = p - 1 ∧ g * z * g⁻¹ = z ^ a ∧
      ∀ d ∈ D, d ∉ zpowers z → ∃ c : ℕ, g * d * g⁻¹ = d ^ b * z ^ c

@[expose] def CentralizerEmbeds {H : Type*} [Group H] (D : Subgroup H) (z : H) : Prop :=
  ∀ d ∈ D, d ∉ zpowers z →
    ∃ f : centralizer ({d} : Set H) →* centralizer ({z} : Set H), Function.Injective f

@[expose] def KFactLemma212 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H],
    CFSG.AGLEmbedding.CatalogSimpleSections H → ∀ (P : Sylow p H) (z : H) (D : Subgroup H),
      Lemma212Config p P z D → (∃ g, IsPlaneDiagonal p D z g) →
        HasPrimeConstraint (G := H) p ∨
          CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥

@[expose] def KFactLemma213 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H],
    CFSG.AGLEmbedding.CatalogSimpleSections H → ¬ HasPrimeConstraint (G := H) p →
      CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ →
      ∀ (P : Sylow p H) (z : H) (D : Subgroup H), Lemma212Config p P z D →
        (∃ g, IsPlaneDiagonal p D z g) → CentralizerEmbeds D z →
        (∀ T : Subgroup H, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set H) →
            T ≤ primeComplementCore (G := H) p) ∨
          (∀ y ∈ D, y ≠ 1 → ∃ h ∈ normalizer (D : Set H),
            zpowers y = (zpowers z).map (MulAut.conj h).toMonoidHom)

structure Bal3KFacts : Prop where
  lemma212 : KFactLemma212
  lemma213 : KFactLemma213

variable {G : Type} [Group G] [Finite G]

@[expose] def Bal3Residue (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) → IsMulCommutative D →
      ∀ z ∈ D, z ≠ 1 → z ∈ centralizer (P : Set G) → z ^ p = 1 →
        normalizer ((zpowers z : Subgroup G) : Set G) ≤ M → ¬ HasPrimeConstraint (G := M) p →
        ¬ ((P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D) →
        ∀ T : Subgroup G, invariantTwoMaximalWithin D M T →
          ((5 ≤ p ∨ CFSG.ABGLocalTools.IsPConstrained p
              (normalizer ((zpowers z : Subgroup G) : Set G))) →
            ∀ d ∈ D, d ≠ 1 → T ⊓ centralizer ({d} : Set G) ≤
              CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers d : Subgroup G) : Set G))) →
          T ≤ CFSG.ABGTheoremB.pPrimeCoreIn p M ⊔
            CFSG.ABGTheoremB.pPrimeCoreIn p (normalizer ((zpowers z : Subgroup G) : Set G))

end CFSG.LocalAnalysis.RankThreeTheoremC
