module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStar
public import CFSG.LocalAnalysis.AGLEmbedding.SocleConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Unitary

variable {G : Type} [Group G] [Finite G]

theorem IsUnitaryIndex.exists_eq {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (h : IsUnitaryIndex p d) :
    ∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q ∧
      d.1.fieldExponent = q.exponent ∧ 1 ≤ q.exponent := by
  obtain ⟨q, hp, hd⟩ := h
  exact ⟨q, hp, hd, by rw [hd]; simp, q.exponent_pos⟩

@[expose] def KFactUnitarySchur : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ) (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Open.IsQuasisimple K → IsPGroup p (Subgroup.center K) →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    Subgroup.center K = ⊥

@[expose] def KFactUnitarySylowStructure : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    p ≠ 2 → IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → ∀ U : Sylow p L,
    Nat.card (U : Subgroup L) = p ^ (3 * d.1.fieldExponent) ∧
    ⁅(U : Subgroup L), (U : Subgroup L)⁆ =
        (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) ∧
      (∀ u ∈ (U : Subgroup L), u ^ p = 1) ∧
      ∃ E : Subgroup L, E ≤ U ∧ IsElemAbelian p E ∧ Nat.card E = p ^ (2 * d.1.fieldExponent)

@[expose] def KFactUnitarySylowCenterTorus : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → ∀ U : Sylow p L,
    ∃ ψ : Multiplicative (GaloisField p d.1.fieldExponent) →* L, Function.Injective ψ ∧
      ψ.range = (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) ∧
      ∀ μ : (GaloisField p d.1.fieldExponent)ˣ,
        ∃ c ∈ Subgroup.normalizer ((U : Subgroup L) : Set L),
          ∀ a : Multiplicative (GaloisField p d.1.fieldExponent),
            c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd
              ((μ : GaloisField p d.1.fieldExponent) * Multiplicative.toAdd a))

@[expose] def KFactUnitaryTorusPPD : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → 2 ≤ d.1.fieldExponent → Nonempty (L ≃* CatGroup d) →
    ∀ (U : Sylow p L) (r : ℕ), r.Prime →
    r ∣ p ^ (2 * d.1.fieldExponent) - 1 →
    (∀ k : ℕ, 0 < k → k < 2 * d.1.fieldExponent → ¬ r ∣ p ^ k - 1) →
    ∃ c ∈ Subgroup.normalizer ((U : Subgroup L) : Set L), orderOf c = r ∧
      ∀ k : ℕ, ¬ r ∣ k →
        (∃ u ∈ (U : Subgroup L), c ^ k * u * (c ^ k)⁻¹ * u⁻¹ ∉
          (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L)) ∧
        ∀ V : Subgroup L,
          (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) ≤ V → V ≤ U →
          c ^ k ∈ Subgroup.normalizer (V : Set L) →
          V = (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) ∨ V = U

@[expose] def KFactUnitaryUnipotentCentralizer : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → ∀ (U : Sylow p L) (α : MulAut L),
    (∀ u ∈ (U : Subgroup L), α u = u) → ∃ u ∈ (U : Subgroup L), α = MulAut.conj u

@[expose] def KFactUnitaryBorelMaximal : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → ∀ U : Sylow p L,
    IsCoatom (Subgroup.normalizer ((U : Subgroup L) : Set L))

@[expose] def KFactUnitaryBorelPCore : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → ∀ (U : Sylow p L)
    (A : Subgroup (MulAut L)), IsPGroup p A →
    (∀ b ∈ Subgroup.normalizer ((U : Subgroup L) : Set L), ∀ α ∈ A,
      MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ A) →
    ∀ α ∈ A, ∃ u ∈ (U : Subgroup L), α = MulAut.conj u

@[expose] def KFactUnitarySylowNormalizerSolvable : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → ∀ (U : Sylow p L)
    (A : Subgroup (MulAut L)),
    (∀ α ∈ A, (U : Subgroup L).map (α : L ≃* L).toMonoidHom = U) → Group.IsSolvable A

@[expose] def KFactUnitaryAutElemRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → ∀ E : Subgroup (MulAut L),
    IsElemAbelian p E → Nat.card E ≤ p ^ (2 * d.1.fieldExponent)

@[expose] def KFactUnitaryAutPCard : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex),
    p ≠ 2 → IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → ∀ S : Subgroup (MulAut L),
    IsPGroup p S → Nat.card S ∣ p ^ (3 * d.1.fieldExponent) * d.1.fieldExponent

@[expose] def KFactUnitaryOrder : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) →
    Nat.card L * Nat.gcd 3 (p ^ d.1.fieldExponent + 1) =
      (p ^ d.1.fieldExponent) ^ 3 * ((p ^ d.1.fieldExponent) ^ 3 + 1) *
        ((p ^ d.1.fieldExponent) ^ 2 - 1)

open CFSG.ComponentClassification.OuterAutomorphisms in
@[expose] def KFactUnitaryOuterSolvable : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (p : ℕ) (d : TauCeti.ValidLieTypeIndex),
    IsUnitaryIndex p d → Nonempty (L ≃* CatGroup d) → Group.IsSolvable (Outer L)

@[expose] def KFactJStarElimUnitaryLie : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (d₀ : TauCeti.ValidLieTypeIndex), p ≠ 2 → IsUnitaryIndex p d₀ →
    2 ≤ d₀.1.fieldExponent → ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
    ∀ d : TauCeti.ValidLieTypeIndex, P1ThreeLieList p d → ¬ IsUnitaryIndex p d →
    Nonempty (L ≃* CatGroup d) →
    ¬ JStarElimDataOf L p (p ^ (3 * d₀.1.fieldExponent) * d₀.1.fieldExponent) (CatGroup d₀)

@[expose] def KFactJStarElimUnitaryAlt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (d₀ : TauCeti.ValidLieTypeIndex), p ≠ 2 → IsUnitaryIndex p d₀ →
    2 ≤ d₀.1.fieldExponent → ∀ (L : Type) [Group L] [Finite L],
    Nonempty (L ≃* alternatingGroup (Fin (3 * p))) →
    ¬ JStarElimDataOf L p (p ^ (3 * d₀.1.fieldExponent) * d₀.1.fieldExponent) (CatGroup d₀)

@[expose] def KFactJStarElimUnitarySpor : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (d₀ : TauCeti.ValidLieTypeIndex), p ≠ 2 → IsUnitaryIndex p d₀ →
    2 ≤ d₀.1.fieldExponent → ∀ (L : Type) [Group L] [Finite L],
    ∀ s : TauCeti.SporadicName, P1ThreeSporList p s →
    Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ¬ JStarElimDataOf L p (p ^ (3 * d₀.1.fieldExponent) * d₀.1.fieldExponent) (CatGroup d₀)

@[expose] def StmtUnitarySocle : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex, IsUnitaryIndex p d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        IsSimpleGroup K ∧ Nonempty (K ≃* CatGroup d) ∧
          D1SocleConfig K p P M H R (d1LiftX p H R K)

@[expose] def StmtUnitaryBorel : Prop :=
  ∀ {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime] (Rb : Sylow p Y)
    (Y₀ K Ub Zb : Subgroup Y) (d : TauCeti.ValidLieTypeIndex), IsUnitaryIndex p d →
    ReducedNongeneration p Y Rb Y₀ → K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ →
    Ub = (Rb : Subgroup Y) ⊓ K → Zb = Ub ⊓ Subgroup.centralizer (Ub : Set Y) →
    2 ≤ d.1.fieldExponent ∧ Nat.card Ub = p ^ (3 * d.1.fieldExponent) ∧ ⁅Ub, Ub⁆ = Zb ∧
    (∀ u ∈ Ub, u ^ p = 1) ∧
    (∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) → W = ⊥ ∨ Zb ≤ W) ∧
    (∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) → IsPGroup p W →
      W ≤ Ub) ∧
    Subgroup.centralizer (Ub : Set Y) ≤ Ub ∧
    (∃ ψ : Multiplicative (GaloisField p d.1.fieldExponent) →* Y, Function.Injective ψ ∧
      ψ.range = Zb ∧ ∀ μ : (GaloisField p d.1.fieldExponent)ˣ, ∃ c ∈ Y₀,
        ∀ a : Multiplicative (GaloisField p d.1.fieldExponent),
          c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd
            ((μ : GaloisField p d.1.fieldExponent) * Multiplicative.toAdd a))) ∧
    (∀ r : ℕ, r.Prime → r ∣ p ^ (2 * d.1.fieldExponent) - 1 →
      (∀ k : ℕ, 0 < k → k < 2 * d.1.fieldExponent → ¬ r ∣ p ^ k - 1) →
      ∃ c ∈ Y₀, c ∈ Subgroup.normalizer (Ub : Set Y) ∧ orderOf c = r ∧
        ∀ k : ℕ, ¬ r ∣ k → (∃ u ∈ Ub, c ^ k * u * (c ^ k)⁻¹ * u⁻¹ ∉ Zb) ∧
          ∀ V : Subgroup Y, Zb ≤ V → V ≤ Ub → c ^ k ∈ Subgroup.normalizer (V : Set Y) →
            V = Zb ∨ V = Ub) ∧
    Group.IsSolvable Y₀ ∧ Open.pRank p (⊤ : Subgroup Y) ≤ 2 * d.1.fieldExponent

structure D1UnitaryData (p : ℕ) [Fact p.Prime] (n : ℕ) (P : Sylow p G)
    (M H R U X : Subgroup G) : Prop where
  ph3 : D1PhaseThree p P M H R
  ind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q
  two_le : 2 ≤ n
  le_R : U ≤ R
  center_eq : X = U ⊓ Subgroup.centralizer (U : Set G)
  le_nclIn : U ≤ nclIn H X
  card_eq : Nat.card U = p ^ (3 * n)
  commutator_eq : ⁅U, U⁆ = X
  pow_eq_one : ∀ u ∈ U, u ^ p = 1
  torus : ∃ φ : Multiplicative (GaloisField p n) ≃* X, ∀ μ : (GaloisField p n)ˣ,
    ∃ t ∈ H ⊓ M, ∀ a : Multiplicative (GaloisField p n),
      t * (φ a : G) * t⁻¹ =
        φ (Multiplicative.ofAdd ((μ : GaloisField p n) * Multiplicative.toAdd a))
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y
  pcore_le : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    (∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ GLBPrimeCore p H) → Y ≤ U ⊔ GLBPrimeCore p H
  pRank_le : Open.pRank p (H ⊓ M) ≤ 2 * n
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H
  ppd : ∃ (r : ℕ) (t : G), r.Prime ∧ 2 * n < r ∧ r ≠ p ∧ ¬ r ∣ p - 1 ∧ t ∈ H ⊓ M ∧
    t ∈ Subgroup.normalizer (U : Set G) ∧ IsPGroup r (Subgroup.zpowers t) ∧
    (∀ u ∈ U, t ^ r * u * (t ^ r)⁻¹ = u) ∧ (∃ u ∈ U, t * u * t⁻¹ * u⁻¹ ∉ X) ∧
    ∀ V : Subgroup G, X ≤ V → V ≤ U → t ∈ Subgroup.normalizer (V : Set G) → V = X ∨ V = U

@[expose] def StmtUnitaryData : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {d : TauCeti.ValidLieTypeIndex},
    IsUnitaryIndex p d → ∀ {T : Type} [Group T] [Finite T], Nonempty (T ≃* CatGroup d) →
    IsSimpleGroup T → ∀ {P : Sylow p G} {M H R U : Subgroup G},
    D1SocleConfig T p P M H R U → (∀ q ∈ GLBBetaFour G, q < p → D1At G q) →
    D1UnitaryData p d.1.fieldExponent P M H R U (U ⊓ Subgroup.centralizer (U : Set G))

@[expose] def StmtUnitaryToJConfig : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {d : TauCeti.ValidLieTypeIndex},
    IsUnitaryIndex p d → ∀ {T : Type} [Group T] [Finite T], Nonempty (T ≃* CatGroup d) →
    ∀ {P : Sylow p G} {M H R U : Subgroup G}, D1SocleConfig T p P M H R U →
    ((U ⊔ pCoreOf 2 M).subgroupOf M).Normal → D1JConfig p P M H R U

@[expose] def StmtUnitaryTarget : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex), p ≠ 2 → IsUnitaryIndex p d →
    2 ≤ d.1.fieldExponent → ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* CatGroup d) →
    IsSimpleGroup T →
    JStarTarget p (p ^ (3 * d.1.fieldExponent) * d.1.fieldExponent) T ∧
    JStarTargetCard p (3 * d.1.fieldExponent) (p ^ (3 * d.1.fieldExponent) * d.1.fieldExponent) T

@[expose] def StmtUnitaryElim : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (d : TauCeti.ValidLieTypeIndex), p ≠ 2 → IsUnitaryIndex p d →
    2 ≤ d.1.fieldExponent → ∀ (T : Type) [Group T] [Finite T], Nonempty (T ≃* CatGroup d) →
    IsSimpleGroup T → JStarElimOf p (p ^ (3 * d.1.fieldExponent) * d.1.fieldExponent) T

end Unitary

end CFSG.AGLEmbedding
