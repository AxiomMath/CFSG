module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrFusionBridge
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def ThompsonBurgoyneInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L →
      (∃ n : ℕ, Odd n ∧ 9 ≤ n ∧ Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n))) ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
        Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2)

@[expose] def SolomonAlternatingInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ¬ ∃ (x : X) (L : Subgroup X) (n : ℕ), orderOf x = 2 ∧ 8 ≤ n ∧
      L ≤ centralizer ({x} : Set X) ∧ IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) ∧
      Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin n))

@[expose] def ClassicalInvolutionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (Open.genFittingFStar G)],
    (∃ a b : Open.genFittingFStar G, a * b ≠ b * a) →
    ∀ z : G, orderOf z = 2 → ∀ J : Subgroup G, z ∈ J →
    Open.IsSubnormal J (centralizer ({z} : Set G)) → ∀ S : Sylow 2 J,
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    (Open.classicalInvolutionWitness J → Blueprint.OddLieType (Open.genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (Open.genFittingFStar G) .M11) ∧
    (Open.classicalInvolutionTightlyEmbedded J → Blueprint.OddLieType (Open.genFittingFStar G) ∨
      Blueprint.NativeSporadic.IsSporadic (Open.genFittingFStar G) .M11 ∨
      Blueprint.NativeSporadic.IsSporadic (Open.genFittingFStar G) .M12)

@[expose] def HarrisSolomonFritzInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ∀ t : X, orderOf t = 2 → ∀ L : Subgroup X, L ≤ centralizer ({t} : Set X) →
    IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) →
    IsSimpleGroup (L ⧸ pPrimeCore 2 L) → pRank 2 (L ⧸ pPrimeCore 2 L) = 2 →
    (∃ P : Sylow 2 (L ⧸ pPrimeCore 2 L), Nat.card (P : Subgroup (L ⧸ pPrimeCore 2 L)) = 8) →
    (∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L))) →
    Blueprint.OddLieType X ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6)) ∧
        Nonempty (X ≃* Blueprint.NativeSporadic.HS))

@[expose] def HarrisSolomonFritzA7Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ∀ t : X, orderOf t = 2 → ∀ L : Subgroup X, L ≤ centralizer ({t} : Set X) →
    IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set X))) →
    Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) →
    (∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L))) →
    Blueprint.OddLieType X ∨
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6)) ∧
        Nonempty (X ≃* Blueprint.NativeSporadic.HS))

@[expose] def FooteInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    ∀ x : X, orderOf x = 2 → ∀ L : Subgroup X, L ≤ centralizer ({x} : Set X) →
    IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) → GSMaximalComponent L →
    (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) →
    Blueprint.OddLieType X ∨ pRank 2 ↥(coreActionKernel L) = 1 ∨
      (Nonempty (X ≃* alternatingGroup (Fin 9)) ∧
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5))) ∨
      (Nonempty (X ≃* alternatingGroup (Fin 10)) ∧
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 6))) ∨
      (Nonempty (X ≃* alternatingGroup (Fin 11)) ∧
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))) ∨
      (Nonempty (X ≃* Blueprint.NativeSporadic.J2) ∧
        Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5)))

@[expose] def TheoremBInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    (∀ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J →
      (Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
        Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2) →
      ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
          Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∧
        ∃ (b : X) (L : Subgroup X) (ρ e : ℕ), orderOf b = 2 ∧ L ≤ centralizer ({b} : Set X) ∧
          IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set X))) ∧ ρ.Prime ∧ ρ ≠ 2 ∧
          1 ≤ e ∧ Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 ρ (2 * e) ∧
          zpowers b ≤ coreActionKernel L ∧
          ∃ P : Sylow 2 ↥(coreActionKernel L),
            (P : Subgroup _) = (zpowers b).subgroupOf (coreActionKernel L)) ∨
      ((∀ b : X, orderOf b = 2 → b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
          (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
          ∃ K : Subgroup X, UnbalancedGS.GSIsoCorr a J b K) ∧
        ∀ (b : X) (K : Subgroup X), orderOf b = 2 →
          b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
          (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
          UnbalancedGS.GSIsoCorr a J b K →
          ∀ S : Subgroup X, S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
            (∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
              (P : Subgroup _) =
                S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) →
            b ∈ S → (∀ s ∈ S, s * b = b * s) →
            S ≤ centralizer ({b} : Set X) ⊓ normalizer (K : Set X) ∧
              ∃ P : Sylow 2 ↥(centralizer ({b} : Set X) ⊓ normalizer (K : Set X)),
                (P : Subgroup _) =
                  S.subgroupOf (centralizer ({b} : Set X) ⊓ normalizer (K : Set X)))) ∧
    ∀ (a : X) (J : Subgroup X), orderOf a = 2 → J ≤ centralizer ({a} : Set X) →
      IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))) →
      Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) →
      ∀ E : Subgroup X, E ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
        Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →
        ⁅J, centralizer ({a} : Set X) ⊓ ⨅ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
            (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype⁆ =
          J →
        ∃ n : ℕ, Odd n ∧ 11 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def TheoremBBoundedInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J →
      (∀ (u v : X) (K : Subgroup X), GSUnbalancingTriple u v K →
        (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index) →
      (Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)) ∨
        (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∨
        Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2) →
      ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
          Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) ∧
        ∃ (b : X) (L : Subgroup X) (ρ e : ℕ), orderOf b = 2 ∧ L ≤ centralizer ({b} : Set X) ∧
          IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set X))) ∧ ρ.Prime ∧ ρ ≠ 2 ∧
          1 ≤ e ∧ Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 ρ (2 * e) ∧
          zpowers b ≤ coreActionKernel L ∧
          ∃ P : Sylow 2 ↥(coreActionKernel L),
            (P : Subgroup _) = (zpowers b).subgroupOf (coreActionKernel L)) ∨
      ((∀ b : X, orderOf b = 2 → b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
          (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
          ∃ K : Subgroup X, UnbalancedGS.GSIsoCorr a J b K) ∧
        ∀ (b : X) (K : Subgroup X), orderOf b = 2 →
          b ∈ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
          (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
          UnbalancedGS.GSIsoCorr a J b K →
          ∀ S : Subgroup X, S ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) →
            (∃ P : Sylow 2 ↥(centralizer ({a} : Set X) ⊓ normalizer (J : Set X)),
              (P : Subgroup _) =
                S.subgroupOf (centralizer ({a} : Set X) ⊓ normalizer (J : Set X))) →
            b ∈ S → (∀ s ∈ S, s * b = b * s) →
            S ≤ centralizer ({b} : Set X) ⊓ normalizer (K : Set X) ∧
              ∃ P : Sylow 2 ↥(centralizer ({b} : Set X) ⊓ normalizer (K : Set X)),
                (P : Subgroup _) =
                  S.subgroupOf (centralizer ({b} : Set X) ⊓ normalizer (K : Set X)))

theorem theoremBBoundedInput_of_theoremBInput (h : TheoremBInput) : TheoremBBoundedInput :=
  fun X _ _ _ hnonab hK hz hU a x J hJ _ htype => (h X hnonab hK hz hU).1 a x J hJ htype

@[expose] def HarrisInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ¬ ∃ (x : X) (L : Subgroup X), orderOf x = 2 ∧ L ≤ centralizer ({x} : Set X) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) ∧ GSMaximalComponent L ∧
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) ∧
      ∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L))

@[expose] def GriessSolomonInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ¬ ∃ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
        Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2)

@[expose] def GloballyFirstRankTwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Assembly.KProper Blueprint.Catalog G →
    (∀ z : G, orderOf z = 2 → z ∉ center G) →
    ∀ (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J → 2 ≤ pRank 2 ↥J →
    (∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index) →
    (∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K → GSReach J K →
      (pPrimeCore 2 K).index = (pPrimeCore 2 J).index →
      pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K) ≤
        pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J)) →
    (∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K → GSReach J K →
      (pPrimeCore 2 K).index = (pPrimeCore 2 J).index →
      pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K) =
        pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) →
      2 ^ (Nat.card ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G))).factorization 2 ≤
        2 ^ (Nat.card ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G))).factorization 2) →
    GSMaximalUnbalancingTriple a x J

end CFSG.ComponentClassification.GSLit
