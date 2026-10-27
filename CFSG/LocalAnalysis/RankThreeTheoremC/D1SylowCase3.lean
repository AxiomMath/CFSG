module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CentralizerComponent3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal ReducedNongeneration CatalogSimpleSections RankOneLieAutFacts
  KGenThree KOutTwoGroup)

variable {G : Type} [Group G] [Finite G]

structure D1SylowComponentData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  glob : Setting G
  loc : D1Local3 p P M
  ext : D1Extremal p P M H (P : Subgroup G)
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

structure D1SylowBetaData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  data : D1SylowComponentData3 p P M H z Pbar zbar K
  not_mem : zbar ∉ K
  center_eq_bot : Subgroup.center K = ⊥
  cyclic : IsCyclic ((Pbar : Subgroup (ReducedCentralizer p z)) ⊓
    Subgroup.centralizer (K : Set (ReducedCentralizer p z)) : Subgroup (ReducedCentralizer p z))

structure D1SylowAlphaData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  data : D1SylowComponentData3 p P M H z Pbar zbar K
  mem : zbar ∈ K
  center_ne_bot : Subgroup.center K ≠ ⊥
  center_cyclic : IsCyclic (Subgroup.center K)
  omega : ∀ c ∈ (Pbar : Subgroup (ReducedCentralizer p z)) ⊓
      Subgroup.centralizer (K : Set (ReducedCentralizer p z)), orderOf c = p →
    c ∈ Subgroup.zpowers zbar

namespace D1SylowComponentData3

variable {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H : Subgroup G} {z : G}
  {Pbar : Sylow p (ReducedCentralizer p z)} {zbar : ReducedCentralizer p z}
  {K : Subgroup (ReducedCentralizer p z)}

theorem betaData (h : D1SylowComponentData3 p P M H z Pbar zbar K) (hzK : zbar ∉ K) :
    D1SylowBetaData3 p P M H z Pbar zbar K := by
  have hZ := (h.red.center_eq_bot_and_rankOne_of_not_mem h.zbar_mem_center h.zbar_order h.comp
    hzK).1
  exact ⟨h, hzK, hZ, h.red.isCyclic_inf_centralizer_of_not_mem_of_center h.zbar_mem_center
    h.zbar_order h.comp h.normal hzK hZ⟩

theorem alphaData (h : D1SylowComponentData3 p P M H z Pbar zbar K) (hzK : zbar ∈ K) :
    D1SylowAlphaData3 p P M H z Pbar zbar K :=
  ⟨h, hzK, CFSG.AGLEmbedding.center_ne_bot_of_mem Fact.out h.zbar_mem_center h.zbar_order hzK,
    h.red.isCyclic_center h.comp h.normal,
    h.red.mem_zpowers_of_mem_inf_centralizer h.zbar_mem_center h.zbar_order h.comp h.normal hzK⟩

end D1SylowComponentData3

@[expose] def D1SylowBetaSmallCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1SylowBetaData3 p P M H z Pbar zbar K → ¬ RankOneLieAutFacts p K →
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → False

@[expose] def D1SylowAlphaNone3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1SylowAlphaData3 p P M H z Pbar zbar K → False

@[expose] def D1SylowComponentCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H : Subgroup G, D1Extremal p P M H (P : Subgroup G) →
      ∀ (_ : Fact p.Prime) (z : G), D1CentralizerInput3 p P M z →
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) ≠ ⊥ → False

@[expose] def D1SylowConstrainedCase3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G),
    IsCoreMaxLocal p P M → ∀ H : Subgroup G, D1Extremal p P M H (P : Subgroup G) →
      ∀ (_ : Fact p.Prime) (z : G), D1CentralizerInput3 p P M z →
      CFSG.layer (Subgroup.centralizer ({z} : Set G) ⧸
        primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) = ⊥ → False

theorem d1SylowComponentCase3_of_cases (hK3 : KFactsA3 G)
    (hbs : D1SylowBetaSmallCase3 G) (hnone : D1SylowAlphaNone3 G) : D1SylowComponentCase3 G := by
  intro hS p hp P M hM H hext hfact z hz hlayer
  obtain ⟨Pbar, zbar, hPbar, hred, hzbar, hzZ, hzp, hX, -, -, E, _, hER, hEcard, hEexp, hEZ, e,
    hSL⟩ := hz.exists_reduced_data hS.simple hS.nonab hS.kProper
  obtain ⟨K, hK⟩ := CFSG.AGLEmbedding.exists_isComponentOf_of_layer_ne_bot hlayer
  have hKn : K.Normal := hred.normal_of_isComponentOf_of_center hzZ hzp hK
  have hKu : ∀ L : Subgroup (ReducedCentralizer p z), IsComponentOf L ⊤ → L = K := fun L hL =>
    hred.eq_of_isComponentOf_of_center hzZ hzp hL hK
  have hdata : D1SylowComponentData3 p P M H z Pbar zbar K :=
    ⟨hS, ⟨hp, hM.1, hM.2⟩, hext, hz, hPbar, hred, hzbar, hzZ, hzp, hX, hK, hKn, hKu⟩
  by_cases hzK : zbar ∈ K
  · exact hnone p P M H z Pbar zbar K (hdata.alphaData hzK)
  ·
    have hbeta := hdata.betaData hzK
    obtain ⟨-, -, hAut⟩ := pRank_mulAut_le_two_of_not_mem hred (hz.pRank_pbar_le_three hPbar) hX
      hzZ hzp hK hKn hzK hK3.beta
    by_cases hfacts : RankOneLieAutFacts p K
    · exact CFSG.AGLEmbedding.false_of_rankOneLieAutFacts hred.ne_two hbeta.center_eq_bot hfacts
        hEcard hEexp (CFSG.AGLEmbedding.inf_centralizer_eq_center_map_of_isCyclic hER hEexp hEZ
          hzZ hzp hbeta.cyclic) e hSL
    · exact hbs p P M H z Pbar zbar K hbeta hfacts hAut

structure D1SylowResidues3 (G : Type) [Group G] [Finite G] : Prop where
  constrained : D1SylowConstrainedCase3 G
  betaSmall : D1SylowBetaSmallCase3 G
  alphaNone : D1SylowAlphaNone3 G

theorem d1SylowResidues3_of_theoremD1 (hD1 : TheoremD1 G) : D1SylowResidues3 G := by
  refine ⟨?_, ?_, ?_⟩
  · intro hS p hp P M hM H hext _ z hz
    exact fun _ => (false_of_extremal_of_theoremD1 hD1 hS hp hM hext).elim
  · intro p _ P M H z Pbar zbar K hd
    exact fun _ _ => (false_of_extremal_of_theoremD1 hD1 hd.data.glob hd.data.loc.sigma
      hd.data.loc.isCoreMaxLocal hd.data.ext).elim
  · intro p _ P M H z Pbar zbar K hd
    exact (false_of_extremal_of_theoremD1 hD1 hd.data.glob hd.data.loc.sigma
      hd.data.loc.isCoreMaxLocal hd.data.ext).elim

end CFSG.LocalAnalysis.RankThreeTheoremC
