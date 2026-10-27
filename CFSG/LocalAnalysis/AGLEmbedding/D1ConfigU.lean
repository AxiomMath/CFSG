module

public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure D1LocalU {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) :
    Prop where
  sigma : p ∈ rankThreeSigmaA G
  maxLocal : GLBIsMaxTwoLocal M
  core : GLBWeakCore p (P : Subgroup G) ≤ M

namespace D1LocalU

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem prime (h : D1LocalU p P M) : p.Prime :=
  CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p h.sigma

theorem ne_two (h : D1LocalU p P M) : p ≠ 2 :=
  CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd p h.sigma

theorem toD1Local (h : D1LocalU p P M) (h4 : 4 ≤ evenRank G) : D1Local p P M :=
  ⟨mem_betaFour_of_mem_sigmaA h4 h.sigma, h.maxLocal, h.core⟩

end D1LocalU

theorem D1Local.toU {p : ℕ} {P : Sylow p G} {M : Subgroup G} (h : D1Local p P M) :
    D1LocalU p P M :=
  ⟨mem_sigmaA_of_mem_betaFour h.beta, h.maxLocal, h.core⟩

structure D1ComponentConfigU {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M H R : Subgroup G) (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  glob : D1GlobalU G
  loc : D1LocalU p P M
  ext : D1Extremal p P M H R
  notCon : ¬ HasPrimeConstraint (G := H) p
  ind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At G q
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
  catalog : CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p)

section Config

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfigU.indBetaFour (h : D1ComponentConfigU p P M H R Rbar) :
    ∀ q ∈ GLBBetaFour G, q < p → D1At G q :=
  fun _ hq hqp => h.ind _ (mem_sigmaA_of_mem_betaFour hq) hqp

theorem D1ComponentConfig.toU (h : D1ComponentConfig p P M H R Rbar) :
    D1ComponentConfigU p P M H R Rbar where
  glob := h.glob.toU
  loc := h.loc.toU
  ext := h.ext
  notCon := h.notCon
  ind := fun q hq hqp => h.ind q (mem_betaFour_of_mem_sigmaA h.glob.rank hq) hqp
  rbar := h.rbar
  red := h.red
  catalog := h.catalog

theorem D1ComponentConfigU.toD1ComponentConfig (h : D1ComponentConfigU p P M H R Rbar)
    (h4 : 4 ≤ evenRank G) : D1ComponentConfig p P M H R Rbar where
  glob := h.glob.toD1Global h4
  loc := h.loc.toD1Local h4
  ext := h.ext
  notCon := h.notCon
  ind := h.indBetaFour
  rbar := h.rbar
  red := h.red
  catalog := h.catalog

theorem D1Extremal.exists_componentConfigU (hglob : D1GlobalU G) (hloc : D1LocalU p P M)
    (hext : D1Extremal p P M H R) (hcon : ¬ HasPrimeConstraint (G := H) p)
    (hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At G q) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      D1ComponentConfigU p P M H R Rbar := by
  obtain ⟨Rbar, hRbar, hred⟩ := hext.reducedNongeneration
  exact ⟨Rbar, hglob, hloc, hext, hcon, hind, hRbar, hred,
    (catalogSimpleSections_of_isKProper hglob.kProper H hext.ne_top).quotient _⟩

end Config

section Cases

@[expose] def D1ConstrainedCaseAt (G : Type) [Group G] [Finite G] : Prop :=
  D1GlobalU G → ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1LocalU p P M →
    ∀ H R : Subgroup G, D1Extremal p P M H R → HasPrimeConstraint (G := H) p → False

@[expose] def D1CaseOneSmallAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfigU p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      Subgroup.center K = ⊥ →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
        z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 → False

@[expose] def D1CaseOneLieAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfigU p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      Subgroup.center K = ⊥ →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
        z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) →
      RankOneLieAutFacts p K → False

@[expose] def D1CaseTwoAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfigU p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) → False

@[expose] def D1CaseThreeAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfigU p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) → False

theorem D1ConstrainedCase.toAt (h : D1ConstrainedCase) (h4 : 4 ≤ evenRank G) :
    D1ConstrainedCaseAt G := fun hglob p P M hloc H R hext hcon =>
  h G (hglob.toD1Global h4) p P M (hloc.toD1Local h4) H R hext hcon

theorem D1CaseOneSmall.toAt (h : D1CaseOneSmall) (h4 : 4 ≤ evenRank G) : D1CaseOneSmallAt G :=
  fun p P M H R Rbar hcfg => h G p P M H R Rbar (hcfg.toD1ComponentConfig h4)

theorem D1CaseTwo.toAt (h : D1CaseTwo) (h4 : 4 ≤ evenRank G) : D1CaseTwoAt G :=
  fun p P M H R Rbar hcfg => h G p P M H R Rbar (hcfg.toD1ComponentConfig h4)

theorem D1CaseThree.toAt (h : D1CaseThree) (h4 : 4 ≤ evenRank G) : D1CaseThreeAt G :=
  fun p P M H R Rbar hcfg => h G p P M H R Rbar (hcfg.toD1ComponentConfig h4)

theorem d1CaseOneLie_of_at (h : ∀ (G : Type) [Group G] [Finite G], 4 ≤ evenRank G →
    D1CaseOneLieAt G) : D1CaseOneLie :=
  fun G _ _ p P M H R Rbar hcfg => h G hcfg.glob.rank p P M H R Rbar hcfg.toU

end Cases

end CFSG.AGLEmbedding
