module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (D1Extremal ReducedNongeneration CatalogSimpleSections RankOneLieAutFacts
  KGenThree KOutNormalSylow KOutTwoGroup centerQuotientAction
  catalogSimpleSections_of_isKProper centralizer_singleton_ne_top exists_inf_centralizer_le
  exists_mulEquiv_map_mk map_center_eq_zpowers_mk mem_zpowers_mk_of_mem_centralizer
  orderOf_mk_of_coprime pRank_map_inf_centralizer_le reducedNongeneration_centralizer_of_not_le
  statedSL_le_map_mk)

abbrev ReducedCentralizer {G : Type} [Group G] (p : ℕ) (z : G) : Type :=
  Subgroup.centralizer ({z} : Set G) ⧸
    primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p

variable {G : Type} [Group G] [Finite G]

structure D1CentralizerComponentData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H R : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  glob : Setting G
  loc : D1Local3 p P M
  ext : D1Extremal p P M H R
  ne : R ≠ (P : Subgroup G)
  input : D1CentralizerInput3 p P M z
  odd : Odd (Nat.card (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))))
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

theorem pRank_mulAut_le_two_of_not_mem {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X}
    {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀)
    (hR3 : Open.pRank p (R : Subgroup X) ≤ 3) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hKn : K.Normal) (hzK : z ∉ K) (hKF : KFactBetaRank2) :
    Subgroup.center K = ⊥ ∧
      IsCyclic ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) ∧
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hZ, hrk⟩ := h.center_eq_bot_and_rankOne_of_not_mem hz hzp hK hzK
  have hcycC := h.isCyclic_inf_centralizer_of_not_mem_of_center hz hzp hK hKn hzK hZ
  refine ⟨hZ, hcycC, ?_⟩
  obtain ⟨T, hTne, hT⟩ := exists_sylow_ne_bot_map_eq_inf_of_component3 h hK
  have hcond : IsCyclic (T : Subgroup K) ∨ GLBCore p 1 (T : Subgroup K) ≠ ⊤ := by
    by_cases hTc : IsCyclic (T : Subgroup K)
    · exact Or.inl hTc
    · refine Or.inr ?_
      have hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X) := by
        intro hc
        rw [← hT] at hc
        exact hTc (isCyclic_of_surjective
          (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm (MulEquiv.surjective _))
      obtain ⟨hN, hKX₀⟩ := hrk hnc
      exact h.glbCore_ne_top_of_rankOne hN hKX₀ hT
  have hzR : z ∈ (R : Subgroup X) := CFSG.AGLEmbedding.mem_sylow_of_mem_center hz hzp R
  have hzc : z ∈ Subgroup.centralizer (K : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun k _ => (Subgroup.mem_center_iff.mp hz k)
  exact pRank_mulAut_le_two_of_component3 hX hKF hK hZ hp h.ne_two T hTne
    (pRank_sylow_component_le_two hp (T : Subgroup K) hT hzR hzp hzK hzc hR3) hcond

theorem D1CentralizerInput3.exists_reduced_data {p : ℕ} [Fact p.Prime] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : Open.IsKProper G) {P : Sylow p G}
    {M : Subgroup G} {z : G} (h : D1CentralizerInput3 p P M z) :
    ∃ (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z),
      (Pbar : Subgroup (ReducedCentralizer p z)) = ((P : Subgroup G).subgroupOf
        (Subgroup.centralizer ({z} : Set G))).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      ReducedNongeneration p (ReducedCentralizer p z) Pbar
        (((Subgroup.centralizer ({z} : Set G) ⊓ M).subgroupOf
          (Subgroup.centralizer ({z} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore p))) ∧
      (∀ zC : Subgroup.centralizer ({z} : Set G), (zC : G) = z →
        QuotientGroup.mk' (primeComplementCore (G := Subgroup.centralizer ({z} : Set G)) p) zC =
          zbar) ∧
      zbar ∈ Subgroup.center (ReducedCentralizer p z) ∧ orderOf zbar = p ∧
      CatalogSimpleSections (ReducedCentralizer p z) ∧
      (∀ y ∈ (Pbar : Subgroup (ReducedCentralizer p z)),
        y ∈ Subgroup.centralizer (Pbar : Set (ReducedCentralizer p z)) → orderOf y = p →
          y ∈ Subgroup.zpowers zbar) ∧
      (∃ v ∈ (Pbar : Subgroup (ReducedCentralizer p z)), orderOf v = p ∧
        Open.pRank p ((Pbar : Subgroup (ReducedCentralizer p z)) ⊓
          Subgroup.centralizer ({v} : Set (ReducedCentralizer p z))) ≤ 2) ∧
      ∃ E L : Subgroup (ReducedCentralizer p z),
        E ≤ (Pbar : Subgroup (ReducedCentralizer p z)) ∧ Nat.card E = p ^ 3 ∧
        (∀ x ∈ E, x ^ p = 1) ∧ (Subgroup.center E).map E.subtype = Subgroup.zpowers zbar ∧
        ∃ e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p),
          StatedSL 2 (ZMod p) ≤
            (L.subgroupOf (Subgroup.normalizer (E : Set (ReducedCentralizer p z)))).map
              (centerQuotientAction E e) := by
  have hp : p.Prime := Fact.out
  obtain ⟨D, hDP, hD, hDcard, hzD, hDrank⟩ := h.iv
  obtain ⟨E, hEP, hEcard, hEexp, hEZ, e, hSL⟩ := h.sl
  obtain ⟨Pbar, hPbar, hred, hzbar⟩ := reducedNongeneration_centralizer_of_not_le hp h.ne_two P
    h.sylow_le h.weakCore_le h.pRank_eq.ge h.mem_centralizer h.orderOf_eq h.not_le h.core_le
  have hO := primeComplementCore_coprime (G := Subgroup.centralizer ({z} : Set G)) p
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h.mem_centralizer x hx)
  let zC : Subgroup.centralizer ({z} : Set G) :=
    ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨hzZ, hzbarp⟩ := hzbar zC rfl
  have hEC := hEP.trans hPC
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_mk _ hp hO (P.isPGroup'.to_le hEP) hEC
  obtain ⟨v, hvD, hvp, hvle⟩ :=
    exists_inf_centralizer_le hD hDcard hzD h.orderOf_eq h.mem_centralizer
  have hvP : v ∈ (P : Subgroup G) := hDP hvD
  refine ⟨Pbar, QuotientGroup.mk' _ zC, hPbar, hred, fun zC' hzC' => ?_, hzZ, hzbarp, ?_,
    fun y hy hyc hyp => ?_, ⟨QuotientGroup.mk' _ ⟨v, hPC hvP⟩, ?_, ?_, ?_⟩,
    (E.subgroupOf _).map (QuotientGroup.mk' _),
    ((Subgroup.centralizer ({z} : Set G)).subgroupOf _).map (QuotientGroup.mk' _), ?_,
    (Nat.card_congr φ.toEquiv).symm.trans hEcard, ?_, map_center_eq_zpowers_mk _ hEC φ hφ hEZ, _,
    statedSL_le_map_mk _ hEC le_rfl φ hφ e hSL⟩
  · exact congrArg _ (Subtype.ext hzC')
  · have hz1 : z ≠ 1 := fun hz1 => hp.one_lt.ne (by rw [← h.orderOf_eq, hz1, orderOf_one])
    exact (catalogSimpleSections_of_isKProper hK _
      (centralizer_singleton_ne_top hs hnab hz1)).quotient _
  · refine mem_zpowers_mk_of_mem_centralizer _ hp hO P.isPGroup' hPC h.uniq (hPbar ▸ hy) ?_ hyp
    rw [← hPbar]
    exact hyc
  · rw [hPbar]
    exact ⟨⟨v, hPC hvP⟩, hvP, rfl⟩
  · exact orderOf_mk_of_coprime hp _ hO ((Subgroup.orderOf_coe _).symm.trans hvp)
  · rw [hPbar]
    exact (pRank_map_inf_centralizer_le _ hp hO P.isPGroup' hPC hvP).trans
      ((PreuniquenessRankFour.Helpers.pRank_mono p hp hvle).trans hDrank)
  · rw [hPbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hEP)
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ (Subtype.ext (hEexp c hc))).trans (map_one _)

theorem D1CentralizerInput3.pRank_pbar_le_three {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M : Subgroup G} {z : G} (h : D1CentralizerInput3 p P M z)
    {Pbar : Sylow p (ReducedCentralizer p z)}
    (hPbar : (Pbar : Subgroup (ReducedCentralizer p z)) =
      ((P : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (primeComplementCore p))) :
    Open.pRank p (Pbar : Subgroup (ReducedCentralizer p z)) ≤ 3 := by
  have hp : p.Prime := Fact.out
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp h.mem_centralizer x hx)
  rw [hPbar, CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype hp _
    (primeComplementCore_coprime p), Subgroup.map_subgroupOf_eq_of_le hPC]
  exact h.pRank_eq.le

structure D1CentralizerBetaData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H R : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  data : D1CentralizerComponentData3 p P M H R z Pbar zbar K
  not_mem : zbar ∉ K
  center_eq_bot : Subgroup.center K = ⊥
  cyclic : IsCyclic ((Pbar : Subgroup (ReducedCentralizer p z)) ⊓
    Subgroup.centralizer (K : Set (ReducedCentralizer p z)) : Subgroup (ReducedCentralizer p z))

structure D1CentralizerAlphaData3 {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M H R : Subgroup G) (z : G) (Pbar : Sylow p (ReducedCentralizer p z))
    (zbar : ReducedCentralizer p z) (K : Subgroup (ReducedCentralizer p z)) : Prop where
  data : D1CentralizerComponentData3 p P M H R z Pbar zbar K
  mem : zbar ∈ K
  center_ne_bot : Subgroup.center K ≠ ⊥
  center_cyclic : IsCyclic (Subgroup.center K)
  omega : ∀ c ∈ (Pbar : Subgroup (ReducedCentralizer p z)) ⊓
      Subgroup.centralizer (K : Set (ReducedCentralizer p z)), orderOf c = p →
    c ∈ Subgroup.zpowers zbar

namespace D1CentralizerComponentData3

variable {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R : Subgroup G} {z : G}
  {Pbar : Sylow p (ReducedCentralizer p z)} {zbar : ReducedCentralizer p z}
  {K : Subgroup (ReducedCentralizer p z)}

theorem betaData (h : D1CentralizerComponentData3 p P M H R z Pbar zbar K) (hzK : zbar ∉ K) :
    D1CentralizerBetaData3 p P M H R z Pbar zbar K := by
  have hZ := (h.red.center_eq_bot_and_rankOne_of_not_mem h.zbar_mem_center h.zbar_order h.comp
    hzK).1
  exact ⟨h, hzK, hZ, h.red.isCyclic_inf_centralizer_of_not_mem_of_center h.zbar_mem_center
    h.zbar_order h.comp h.normal hzK hZ⟩

theorem alphaData (h : D1CentralizerComponentData3 p P M H R z Pbar zbar K) (hzK : zbar ∈ K) :
    D1CentralizerAlphaData3 p P M H R z Pbar zbar K :=
  ⟨h, hzK, CFSG.AGLEmbedding.center_ne_bot_of_mem Fact.out h.zbar_mem_center h.zbar_order hzK,
    h.red.isCyclic_center h.comp h.normal,
    h.red.mem_zpowers_of_mem_inf_centralizer h.zbar_mem_center h.zbar_order h.comp h.normal hzK⟩

end D1CentralizerComponentData3

@[expose] def D1CentralizerBetaSmallCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1CentralizerBetaData3 p P M H R z Pbar zbar K → ¬ RankOneLieAutFacts p K →
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → False

@[expose] def D1CentralizerAlphaNone3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)),
    D1CentralizerAlphaData3 p P M H R z Pbar zbar K → False

theorem d1CentralizerComponentCase3_of_cases (hK3 : KFactsA3 G)
    (hbs : D1CentralizerBetaSmallCase3 G) (hnone : D1CentralizerAlphaNone3 G) :
    D1CentralizerComponentCase3 G := by
  intro hS p hp P M hM H R hext hRP hfact z hz hodd hlayer
  obtain ⟨Pbar, zbar, hPbar, hred, hzbar, hzZ, hzp, hX, -, -, E, _, hER, hEcard, hEexp, hEZ, e,
    hSL⟩ := hz.exists_reduced_data hS.simple hS.nonab hS.kProper
  obtain ⟨K, hK⟩ := CFSG.AGLEmbedding.exists_isComponentOf_of_layer_ne_bot hlayer
  have hKn : K.Normal := hred.normal_of_isComponentOf_of_center hzZ hzp hK
  have hKu : ∀ L : Subgroup (ReducedCentralizer p z), IsComponentOf L ⊤ → L = K := fun L hL =>
    hred.eq_of_isComponentOf_of_center hzZ hzp hL hK
  have hdata : D1CentralizerComponentData3 p P M H R z Pbar zbar K :=
    ⟨hS, ⟨hp, hM.1, hM.2⟩, hext, hRP, hz, hodd, hPbar, hred, hzbar, hzZ, hzp, hX, hK, hKn, hKu⟩
  by_cases hzK : zbar ∈ K
  · exact hnone p P M H R z Pbar zbar K (hdata.alphaData hzK)
  ·
    have hbeta := hdata.betaData hzK
    obtain ⟨-, -, hAut⟩ := pRank_mulAut_le_two_of_not_mem hred (hz.pRank_pbar_le_three hPbar) hX
      hzZ hzp hK hKn hzK hK3.beta
    by_cases hfacts : RankOneLieAutFacts p K
    · exact CFSG.AGLEmbedding.false_of_rankOneLieAutFacts hred.ne_two hbeta.center_eq_bot hfacts
        hEcard hEexp (CFSG.AGLEmbedding.inf_centralizer_eq_center_map_of_isCyclic hER hEexp hEZ
          hzZ hzp hbeta.cyclic) e hSL
    · exact hbs p P M H R z Pbar zbar K hbeta hfacts hAut

end CFSG.LocalAnalysis.RankThreeTheoremC
