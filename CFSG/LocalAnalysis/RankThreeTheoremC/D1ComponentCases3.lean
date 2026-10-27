module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1SylowCase3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal ReducedNongeneration CatalogSimpleSections RankOneLieAutFacts
  KGenThree KOutTwoGroup glbPrimeCore_le glbPrimeCore_normal glbPrimeCore_coprime)

variable {G : Type} [Group G] [Finite G]

theorem D1CentralizerInput3.odd_of_ne_sylow {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} (h : D1CentralizerInput3 p P M z) (hext : D1Extremal p P M H R)
    (hRP : R ≠ (P : Subgroup G)) :
    Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))) := by
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h.mem_centralizer x hx)
  exact CFSG.AGLEmbedding.odd_card_of_twoLocals_le hext.prime P.isPGroup' hPC h.not_le
    (glbPrimeCore_le p _) (glbPrimeCore_normal p _) (glbPrimeCore_coprime p _) h.core_le
    fun T hT hT1 hPT => hext.normalizer_le_of_sylow_le hRP hT hT1 hPT

structure D1ComponentData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H R : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  glob : Setting G
  loc : D1Local3 p P M
  ext : D1Extremal p P M H R
  input : D1CentralizerInput3 p P M z
  pbar : (Pbar : Subgroup (ReducedCentralizer p z)) =
    ((P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (ReducedCentralizer p z) Pbar
    (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p)))
  zbar_eq : ∀ zC : Subgroup.centralizer ({z} : Set G), (zC : G) = z →
    QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC = zbar
  zbar_mem_center : zbar ∈ Subgroup.center (ReducedCentralizer p z)
  zbar_order : orderOf zbar = p
  catalog : CatalogSimpleSections (ReducedCentralizer p z)
  comp : IsComponentOf K ⊤
  normal : K.Normal
  unique : ∀ L : Subgroup (ReducedCentralizer p z), IsComponentOf L ⊤ → L = K

structure D1ComponentBetaData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H R : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  data : D1ComponentData3 p P M H R z Pbar zbar K
  not_mem : zbar ∉ K
  center_eq_bot : Subgroup.center K = ⊥
  cyclic : IsCyclic ((Pbar : Subgroup (ReducedCentralizer p z)) ⊓
    Subgroup.centralizer (K : Set (ReducedCentralizer p z)) : Subgroup (ReducedCentralizer p z))

structure D1ComponentAlphaData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H R : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  data : D1ComponentData3 p P M H R z Pbar zbar K
  mem : zbar ∈ K
  center_ne_bot : Subgroup.center K ≠ ⊥
  center_cyclic : IsCyclic (Subgroup.center K)
  omega : ∀ c ∈ (Pbar : Subgroup (ReducedCentralizer p z)) ⊓
      Subgroup.centralizer (K : Set (ReducedCentralizer p z)), orderOf c = p →
    c ∈ Subgroup.zpowers zbar

section Conversions

variable {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G} {z : G}
  {Pbar : Sylow p (ReducedCentralizer p z)} {zbar : ReducedCentralizer p z}
  {K : Subgroup (ReducedCentralizer p z)}

theorem D1CentralizerComponentData3.toMerged
    (h : D1CentralizerComponentData3 p P M H R z Pbar zbar K) :
    D1ComponentData3 p P M H R z Pbar zbar K :=
  ⟨h.glob, h.loc, h.ext, h.input, h.pbar, h.red, h.zbar_eq, h.zbar_mem_center, h.zbar_order,
    h.catalog, h.comp, h.normal, h.unique⟩

theorem D1SylowComponentData3.toMerged (h : D1SylowComponentData3 p P M H z Pbar zbar K) :
    D1ComponentData3 p P M H (P : Subgroup G) z Pbar zbar K :=
  ⟨h.glob, h.loc, h.ext, h.input, h.pbar, h.red, h.zbar_eq, h.zbar_mem_center, h.zbar_order,
    h.catalog, h.comp, h.normal, h.unique⟩

theorem D1CentralizerBetaData3.toMerged (h : D1CentralizerBetaData3 p P M H R z Pbar zbar K) :
    D1ComponentBetaData3 p P M H R z Pbar zbar K :=
  ⟨h.data.toMerged, h.not_mem, h.center_eq_bot, h.cyclic⟩

theorem D1SylowBetaData3.toMerged (h : D1SylowBetaData3 p P M H z Pbar zbar K) :
    D1ComponentBetaData3 p P M H (P : Subgroup G) z Pbar zbar K :=
  ⟨h.data.toMerged, h.not_mem, h.center_eq_bot, h.cyclic⟩

theorem D1CentralizerAlphaData3.toMerged (h : D1CentralizerAlphaData3 p P M H R z Pbar zbar K) :
    D1ComponentAlphaData3 p P M H R z Pbar zbar K :=
  ⟨h.data.toMerged, h.mem, h.center_ne_bot, h.center_cyclic, h.omega⟩

theorem D1SylowAlphaData3.toMerged (h : D1SylowAlphaData3 p P M H z Pbar zbar K) :
    D1ComponentAlphaData3 p P M H (P : Subgroup G) z Pbar zbar K :=
  ⟨h.data.toMerged, h.mem, h.center_ne_bot, h.center_cyclic, h.omega⟩

end Conversions

@[expose] def D1ComponentBetaSmallCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1ComponentBetaData3 p P M H R z Pbar zbar K → ¬ RankOneLieAutFacts p K →
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → False

@[expose] def D1ComponentAlphaSmallCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1ComponentAlphaData3 p P M H R z Pbar zbar K →
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → False

@[expose] def D1ComponentAlphaGenCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1ComponentAlphaData3 p P M H R z Pbar zbar K → KGenThree p K →
    K ≤ ((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
      (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p))

@[expose] def D1ComponentAlphaExpCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1ComponentAlphaData3 p P M H R z Pbar zbar K → KOutTwoGroup K →
    (∀ t ∈ (Pbar : Subgroup (ReducedCentralizer p z)) ⊓ K, t ^ p = 1) →
    Open.pRank p ((Pbar : Subgroup (ReducedCentralizer p z)) ⊓ K) ≤ 3 → False

@[expose] def D1ComponentAlphaNone3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1ComponentAlphaData3 p P M H R z Pbar zbar K → False

theorem D1ComponentBetaSmallCase3.centralizer (h : D1ComponentBetaSmallCase3 G) :
    D1CentralizerBetaSmallCase3 G := by
  intro p _ P M H R z Pbar zbar K hd hnr hAut
  exact h p P M H R z Pbar zbar K hd.toMerged hnr hAut

theorem D1ComponentBetaSmallCase3.sylow (h : D1ComponentBetaSmallCase3 G) :
    D1SylowBetaSmallCase3 G := by
  intro p _ P M H z Pbar zbar K hd hnr hAut
  exact h p P M H (P : Subgroup G) z Pbar zbar K hd.toMerged hnr hAut

theorem D1ComponentAlphaNone3.centralizer (h : D1ComponentAlphaNone3 G) :
    D1CentralizerAlphaNone3 G := by
  intro p _ P M H R z Pbar zbar K hd
  exact h p P M H R z Pbar zbar K hd.toMerged

theorem D1ComponentAlphaNone3.sylow (h : D1ComponentAlphaNone3 G) : D1SylowAlphaNone3 G := by
  intro p _ P M H z Pbar zbar K hd
  exact h p P M H (P : Subgroup G) z Pbar zbar K hd.toMerged

theorem d1MergedCases3_of_theoremD1 (hD1 : TheoremD1 G) :
    D1ComponentBetaSmallCase3 G ∧ D1ComponentAlphaSmallCase3 G ∧ D1ComponentAlphaGenCase3 G ∧
      D1ComponentAlphaExpCase3 G := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p _ P M H R z Pbar zbar K hd
    exact fun _ _ => (false_of_extremal_of_theoremD1 hD1 hd.data.glob hd.data.loc.sigma
      hd.data.loc.isCoreMaxLocal hd.data.ext).elim
  · intro p _ P M H R z Pbar zbar K hd
    exact fun _ => (false_of_extremal_of_theoremD1 hD1 hd.data.glob hd.data.loc.sigma
      hd.data.loc.isCoreMaxLocal hd.data.ext).elim
  · intro p _ P M H R z Pbar zbar K hd
    exact fun _ => (false_of_extremal_of_theoremD1 hD1 hd.data.glob hd.data.loc.sigma
      hd.data.loc.isCoreMaxLocal hd.data.ext).elim
  · intro p _ P M H R z Pbar zbar K hd
    exact fun _ _ _ => (false_of_extremal_of_theoremD1 hD1 hd.data.glob hd.data.loc.sigma
      hd.data.loc.isCoreMaxLocal hd.data.ext).elim

theorem d1ComponentAlphaNone3_of_theoremD1 (hD1 : TheoremD1 G) : D1ComponentAlphaNone3 G := by
  intro p _ P M H R z Pbar zbar K hd
  exact (false_of_extremal_of_theoremD1 hD1 hd.data.glob hd.data.loc.sigma
    hd.data.loc.isCoreMaxLocal hd.data.ext).elim

structure D1MergedResidues3 (G : Type) [Group G] [Finite G] : Prop where
  betaSmall : D1ComponentBetaSmallCase3 G
  alphaNone : D1ComponentAlphaNone3 G
  sylowConstrained : D1SylowConstrainedCase3 G
  constrained : D1CentralizerConstrainedCase3 G
  oneSmall : D1CaseOneSmall3 G
  two : D1CaseTwo3 G
  threeNotKlingen : D1CaseThreeNotKlingen3 G

theorem d1MergedResidues3_of_theoremD1 (hD1 : TheoremD1 G) : D1MergedResidues3 G := by
  obtain ⟨-, -, hcon, h1s, h2, h3⟩ := residues3_of_theoremD1 hD1
  exact ⟨(d1MergedCases3_of_theoremD1 hD1).1, d1ComponentAlphaNone3_of_theoremD1 hD1,
    (d1SylowResidues3_of_theoremD1 hD1).constrained, hcon, h1s, h2, h3⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
