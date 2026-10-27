module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Amb
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFTrivial
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NonConstrainedBranch
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open scoped Pointwise

structure D2L34SideCtx3 (G : Type) [Group G] [Finite G] (d : TauCeti.ValidLieTypeIndex)
    (P : Sylow 3 G) (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Prop where
  setting : Setting G
  d1 : TheoremD1 G
  maxLocal : rankThreeIsMaxTwoLocal M
  fullCore : D2FullCoreAt G M
  threeClause : D2ThreeClauseAt G M
  sigma : 3 ∈ rankThreeSigmaA G
  core : IsCoreMaxLocal 3 P M
  conf : D2L34BetaConf3 d P M A H R Rbar K
  allResidue : D2L34AllResidue3 P M

theorem D2L34SideCtx3.amb {G : Type} [Group G] [Finite G] {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (h : D2L34SideCtx3 G d P M A H R Rbar K) :
    D2Amb3 G :=
  D2Amb3.of_setting h.setting h.d1 h.sigma

@[expose] def D2L34BetaMSolvableCenter3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → Group.IsSolvable M →
    ∃ E : Subgroup G, E ≤ (P : Subgroup G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ x ∈ (P : Subgroup G), x ^ 3 = 1 → ∀ e ∈ E, x * e = e * x

@[expose] def FFRankTwoInput3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M → FFRankTwoCase M T

@[expose] def FFNoncyclicInput3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M →
    CFSG.ABGLocalTools.IsPConstrained 3 ↥M → ∀ T : Subgroup G, IsSylowTwoOf T M →
    ¬ Subgroup.normalizer (T : Set G) ≤ M → ∀ S : Sylow 3 ↥(ffC M T),
      ¬ IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype) →
      ∃ P₀ : Subgroup G, P₀ ≤ M ∧ Nat.card P₀ = 3 ∧
        ((P₀ ⊔ GLBPrimeCore 3 M).subgroupOf M).Normal

@[expose] def D2L34BetaMSideNonConstrainedInput3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (P : Sylow 3 G) (M A H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    D2L34SideCtx3 G d P M A H R Rbar K → GLBStronglyEmbedded 3 M → D2L34Kmax H →
    ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M →
    ∀ U : Subgroup G, IsBetaBase H M U → IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) →
      A ≤ Subgroup.normalizer (U : Set G) → Subgroup.normalizer (U : Set G) ≤ H →
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) →
      ∃ P₁ L : Subgroup G, L ≤ M ∧ (L.subgroupOf M).Normal ∧ P₁ ≤ L ∧
        Nat.card P₁ = 3 ∧ (P₁ : Set G) * U = U * P₁ ∧
        (∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ GLBPrimeCore 3 M) ∧
        SimpleNonabelianModulo L (GLBPrimeCore 3 M)

end CFSG.LocalAnalysis.RankThreeTheoremC
