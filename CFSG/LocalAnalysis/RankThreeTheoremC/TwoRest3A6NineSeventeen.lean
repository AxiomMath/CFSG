module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenCaseTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6KappaCited
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6G23Discharge
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Prop3
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.G23
  CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
  CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem TwoRestG23Config.isAGLQ_centBase (hk : D1CaseTwoKFacts3 G) (h1014 : TwoRestTenFourteen G)
    {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {z : H} {Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L : Subgroup G}
    (cfg : TwoRestG23Config P M H R Rbar z Kbar L) (hRM : R ≤ M) :
    IsAGLQ 3 M (centBase M R L hRM) := by
  have hd := cfg.data
  obtain ⟨h, hzM, -, hz3, hCz, hrk, hcyc, hin⟩ := D1CaseTwoData3.nf_inputs hk.out hk.seitzCyc
    hk.caseTwoLocal hk.inv hk.schreier hk.sylow hk.eightFour hk.eightFive hk.eightSix
    hk.nineThree hk.noXBlock hk.toralThree hd cfg.cand cfg.notSP cfg.outside cfg.b0
    cfg.normalizer_le
  have hRP : R ≤ (P : Subgroup G) := h.toD1Escape.le_P
  have hnorm : (L.subgroupOf M).Normal :=
    TwoRest3A6.normal_of_threeASix h kFactBlockThreeASix_holds hcyc hzM hz3 hCz hin hrk cfg.b0
      hRM cfg.block cfg.center cfg.quot
      (TwoRest3A6.index_centralizer_barM_le_three h kFactBlockThreeASix_holds
        hk.eightFive hk.eightSix hk.nineThree hk.noXBlock hcyc hzM hz3 hCz hin hrk cfg.block
        cfg.center cfg.quot cfg.centV cfg.notShort hRP)
  have hMN : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer cfg.block.le).mp hnorm
  have he := hd.cfg.ext.toD1Escape
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG2 : ∀ a ∈ centBase M R L hRM, a ≠ 1 → a ^ 3 = 1 →
      (∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ a ∈ E) →
      Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ M := by
    intro a ha ha1 ha3 hE
    obtain ⟨E, hER, hEab, hEc, haE⟩ := hE
    have hCM : Subgroup.centralizer ({a} : Set G) ≤ M := by
      by_contra hCM
      apply h1014 P M H R Rbar z Kbar L cfg a ha1 ha3 ⟨E, hER, hEab, hEc, haE⟩ hCM
      rw [Subgroup.commutator_le]
      intro g hg l hl
      rw [commutatorElement_def]
      have hgB : g ∈ centBase M R L hRM := (Subgroup.zpowers_le.mpr ha) hg
      have hgM : g ∈ M := hRM (centBase_le hRM hgB)
      have h1 : g * l * g⁻¹ * l⁻¹ ∈ pCoreOf 2 M := centBase_comm hRM cfg.block.le g hgB l hl
      have h2 : g * l * g⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMN hgM) l).mp hl) (L.inv_mem hl)
      exact inf_le_pCoreOf cfg.block.le ⟨h2, h1⟩
    exact normalizer_zpowers_le he.sylow_le he.weakCore_le haE hEab (hEc.trans (by norm_num)) hCM
  set B := centBase M R L hRM with hBdef
  have hBR : B ≤ R := centBase_le hRM
  have hidx : B.relIndex R ≤ 3 := (block_facts hk cfg hRM).2
  obtain ⟨E, hER, hE, hEcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank
    Nat.prime_three h.toD1Escape.three_le_pRank
  have hrelE : B.relIndex E ≤ 3 := (Subgroup.relIndex_le_of_le_right hER
    (CFSG.GH74.Uniqueness.SU.SU1.relIndex_ne_zero_of_finite B R)).trans hidx
  have hmul := Subgroup.relIndex_mul_card (H := B) (K := E)
  rw [hEcard] at hmul
  obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hEcard ▸ Subgroup.card_dvd_of_le (inf_le_right : B ⊓ E ≤ E))
  have hj2 : 2 ≤ j := by
    by_contra hlt
    interval_cases j <;> rw [hcj] at hmul <;> omega
  obtain ⟨F, hFBE, hF, hFcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_subgroup_card
    Nat.prime_three (CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.mono inf_le_right hE) hj2 hcj
  have hFP : F ≤ (P : Subgroup G) := (hFBE.trans inf_le_left).trans (hBR.trans hRP)
  have hEC : E ≤ F ⊔ ((P : Subgroup G) ⊓ Subgroup.centralizer (F : Set G)) := fun x hx =>
    Subgroup.mem_sup_right ⟨hRP (hER hx), Subgroup.mem_centralizer_iff.mpr fun f hf => by
      have := hE.1.is_comm.comm ⟨f, (hFBE hf).2⟩ ⟨x, hx⟩
      exact congrArg Subtype.val this⟩
  have hNF : Subgroup.normalizer (F : Set G) ≤ M := by
    refine le_trans ?_ h.toD1Escape.weakCore_le
    unfold GLBWeakCore rankThreeAschCore
    exact le_sSup ⟨F, hFP, CFSG.SectionRank.le_pRank (by norm_num) le_rfl hF hFcard,
      CFSG.SectionRank.le_pRank (by norm_num) hEC hE hEcard, rfl⟩
  have hΓ : rankThreeGamma 1 3 F ≤ M := TwoRest3A6.rankThreeGamma_le hF hFcard hNF
    fun a ha ha1 =>
      hG2 a (hFBE ha).1 ha1 (hF.2 a ha) ⟨E, hER, hE, by rw [hEcard]; norm_num, (hFBE ha).2⟩
  exact ⟨hBR.trans hRM, P.isPGroup'.to_le (hBR.trans hRP),
    Or.inr ⟨F, hFBE.trans inf_le_left, hF, hFcard, hΓ⟩⟩

theorem TwoRestG23Config.kbar_facts (hk : D1CaseTwoKFacts3 G) (h1014 : TwoRestTenFourteen G)
    {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {z : H} {Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L : Subgroup G}
    (cfg : TwoRestG23Config P M H R Rbar z Kbar L) (hRM : R ≤ M) :
    innerNotQJ 3 H Kbar = Kbar ∧ IsSimpleGroup Kbar ∧ (∃ a b : Kbar, a * b ≠ b * a) ∧
      (∃ x : Kbar, x ≠ 1 ∧ ∃ k : ℕ, x ^ 3 ^ k = 1) ∧ IsCaseTwoGroup 3 Kbar ∧
      d1Kappa 3 M H ≤ Nat.card Kbar := by
  have hd := cfg.data
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : (centBase M R L hRM).relIndex R ≤ 3 := (block_facts hk cfg hRM).2
  obtain ⟨hKs, hKnab, -⟩ :=
    hd.cfg.red.isSimpleGroup_of_isCyclic hd.cfg.catalog cfg.component (hd.cyclic _ cfg.component)
  have hiso : IsCaseTwoGroup 3 Kbar :=
    hd.cfg.red.isCaseTwoGroup_of_not_le3 hd.cfg.catalog hk.out hk.seitzCyc hd.cyclic hd.rank
      cfg.component cfg.not_le
  obtain ⟨q, -, hqK, hqo, -⟩ := exists_mem_base_inf_component hk hd hidx cfg.component cfg.not_le
  have hKp : ∃ x : Kbar, x ≠ 1 ∧ ∃ k : ℕ, x ^ 3 ^ k = 1 := by
    refine ⟨⟨_, hqK⟩, fun h1 => ?_, 1, Subtype.ext ?_⟩
    · have h1' := congrArg Subtype.val h1
      simp only [OneMemClass.coe_one] at h1'
      rw [h1', orderOf_one] at hqo
      exact absurd hqo (by norm_num)
    · simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
      have := pow_orderOf_eq_one (QuotientGroup.mk' (primeComplementCore (G := H) 3) q)
      rwa [hqo] at this
  have hκ : d1Kappa 3 M H ≤ Nat.card Kbar := by
    unfold d1Kappa
    rw [d1KBar_eq_of_unique cfg.component cfg.not_le fun L' hL' hL'X => by
      by_contra hne
      exact hL'X (le_X0_of_tenFourteen hk h1014 cfg hRM hL' fun h => hne h.symm)]
  exact ⟨innerNotQJ_eq_of_tenFourteen hk h1014 cfg hRM, hKs, hKnab, hKp, hiso, hκ⟩

theorem twoRestNineSeventeen_of_rankTwo (hk : D1CaseTwoKFacts3 G) (h1014 : TwoRestTenFourteen G)
    (h3 : D1CaseThreeNotKlingen3 G) (hother : D1CaseThreeKlingenOther3 G)
    (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel) (h2 : TwoRestRankTwoFactor G) :
    TwoRestNineSeventeen G := by
  intro P M H R Rbar z Kbar L hRM cfg
  obtain ⟨hJ, hKs, hKnab, hKp, hiso, hκ⟩ := cfg.kbar_facts hk h1014 hRM
  have h2' := h2 P M H R Rbar z Kbar L hRM cfg
  rw [hJ] at h2' ⊢
  have hd := cfg.data
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : (centBase M R L hRM).relIndex R ≤ 3 := (block_facts hk cfg hRM).2
  have h917 : Hyp917Ext 3 M H (centBase M R L hRM) Kbar :=
    hyp917Ext_of_caseTwoGroup h3 hother hk.schreier hkl hmod hk.out hk.seitzCyc hk.inv.toIn
      hd.cfg.glob hd.cfg.loc.sigma hd.cfg.ind hKs hKnab hKp hiso
      (by rw [KFactProofs.card_of_isCaseTwoGroup_three hiso]; norm_num) cfg.not_le hκ
  have hBQ := cfg.isAGLQ_centBase hk h1014 hRM
  have hRP : R ≤ (P : Subgroup G) := hd.cfg.ext.toD1Escape.le_P
  have hR3 : Open.pRank 3 R ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hRP).trans hd.cfg.pRank_eq_three.le
  exact hyp917R_of_ext_of_rankTwo hd.cfg.ext (centBase_le hRM) hidx
    (fun U hBU hUM hU => normalizer_le_of_isAGLQ hd.cfg.ext (isAGLQ_of_le hBQ hBU hUM hU)) hR3
    h917 h2'

theorem exists_noncentral_pow_three_of_threeASix {X : Type*} [Group X] [Finite X]
    (hZ : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    ∃ u : X, u ∉ Subgroup.center X ∧ u ^ 3 = 1 := by
  let a : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  let g : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have hga : g * a * g⁻¹ = a⁻¹ := by decide
  have ha3 : a ^ 3 = 1 := by decide
  have ha1 : a ≠ 1 := by decide
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) (e.symm a)
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) (e.symm g)
  have hmem : ∀ y : X, QuotientGroup.mk' (Subgroup.center X) y = 1 →
      y ∈ Subgroup.center X := fun y h =>
    (QuotientGroup.eq_one_iff y).mp h
  have hz3 : ∀ y ∈ Subgroup.center X, y ^ 3 = 1 := fun y hy => by
    have h := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨y, hy⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  set z := u * (x * u * x⁻¹) with hzdef
  have hz : z ∈ Subgroup.center X := hmem _ (by
    have : QuotientGroup.mk' (Subgroup.center X) z = e.symm (a * (g * a * g⁻¹)) := by
      rw [hzdef, map_mul, map_mul, map_mul, map_inv, hu, hx, map_mul, map_mul, map_mul, map_inv]
    rw [this, hga, mul_inv_cancel, map_one])
  have hy : u ^ 3 ∈ Subgroup.center X := hmem _ (by rw [map_pow, hu, ← map_pow, ha3, map_one])
  have hconj : x * u ^ 3 * x⁻¹ = u ^ 3 := by
    rw [Subgroup.mem_center_iff.mp hy x, mul_inv_cancel_right]
  have hxu : x * u * x⁻¹ = u⁻¹ * z := by rw [hzdef, inv_mul_cancel_left]
  have hcomm : Commute u⁻¹ z := Subgroup.mem_center_iff.mp hz u⁻¹
  have h33 : u ^ 3 = u⁻¹ ^ 3 := by
    rw [← hconj, ← conj_pow, hxu, hcomm.mul_pow, hz3 z hz, mul_one]
  have h6 : u ^ 3 * u ^ 3 = 1 := by
    calc u ^ 3 * u ^ 3 = u⁻¹ ^ 3 * u ^ 3 := by rw [← h33]
      _ = 1 := by rw [inv_pow, inv_mul_cancel]
  have h9 := hz3 _ hy
  have h93 : (u ^ 3) ^ 3 = u ^ 3 := by rw [pow_succ, pow_two, h6, one_mul]
  refine ⟨u, fun hu' => ha1 ?_, h93 ▸ h9⟩
  have : QuotientGroup.mk' (Subgroup.center X) u = 1 := (QuotientGroup.eq_one_iff u).mpr hu'
  rw [hu] at this
  simpa using congrArg e this

theorem pRank_centBase_le_two {M R L : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup 3 R)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hq : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hM3 : Open.pRank 3 M ≤ 3) : Open.pRank 3 (centBase M R L hRM) ≤ 2 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨E, hEB, hE, hEc⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp (H := centBase M R L hRM)
      (k := 3) (by omega)
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hEM : E ≤ M := (hEB.trans (centBase_le hRM)).trans hRM
  have hEp : IsPGroup 3 (E.subgroupOf M) :=
    (hR.to_le (hEB.trans (centBase_le hRM))).comap_subtype
  have hker : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp (pCore_isPGroup (G := ↥M) (p := 2)))
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel 3 hp
    (CFSG.pCore 2 ↥M) hker _ hEp
  set Eb := (E.subgroupOf M).map φ
  have hEbc : Nat.card Eb = 3 ^ 3 := by
    rw [← hEc, ← Nat.card_congr (MulEquiv.ofBijective _ ⟨hinj,
      φ.subgroupMap_surjective (E.subgroupOf M)⟩).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
  have hEM' : Open.IsElemAbelian 3 (E.subgroupOf M) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (by
      simpa using congrArg Subtype.val (hE.1.is_comm.comm ⟨(a : M), Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨(b : M), Subgroup.mem_subgroupOf.mp b.2⟩)))⟩⟩,
      fun x hx => Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp hx))⟩
  have hEb : Open.IsElemAbelian 3 Eb := CFSG.Open.IsElemAbelian.map hEM' φ
  have hEbC : Eb ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨⟨r, hr⟩, hrc, hrm⟩ := hEB (Subgroup.mem_subgroupOf.mp hm)
    have : (⟨r, hRM hr⟩ : M) = m := Subtype.ext hrm
    rw [← this]
    exact hrc
  obtain ⟨⟨w, hwL⟩, hwZ, hw3⟩ := exists_noncentral_pow_three_of_threeASix hZ hq.some
  have hw3' : w ^ 3 = 1 := congrArg Subtype.val hw3
  have hwC : w ∈ Subgroup.centralizer (Eb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      (Subgroup.mem_centralizer_iff.mp (hEbC hh) w hwL).symm
  have hwE : w ∉ Eb := fun hw => hwZ (Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEbC hw) y y.2))
  have h4 := succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp hEb hEbc hw3' hwE hwC
    le_top (Subgroup.mem_top w)
  have h5 := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp φ
    (by rw [QuotientGroup.ker_mk']; exact hker) ⊤
  rw [Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective _)] at h5
  obtain ⟨F, -, hF, hFc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp
    (H := (⊤ : Subgroup ↥M)) (k := 4) (by omega)
  have h6 : 4 ≤ Open.pRank 3 M :=
    CFSG.GH74.Uniqueness.SU.SU1.le_pRank (by norm_num) (Subgroup.map_subtype_le F)
      (CFSG.Open.IsElemAbelian.map hF M.subtype)
      (by rw [Subgroup.card_map_of_injective M.subtype_injective, hFc])
  omega

theorem TwoRestG23Config.pRank_centBase_le_two {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} {z : H}
    {Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {L : Subgroup G}
    (cfg : TwoRestG23Config P M H R Rbar z Kbar L) (hRM : R ≤ M) :
    Open.pRank 3 (centBase M R L hRM) ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd := cfg.data
  have hRP : R ≤ (P : Subgroup G) := hd.cfg.ext.toD1Escape.le_P
  have hG : Open.pRank 3 (⊤ : Subgroup G) ≤ 3 := by
    exact pRank_top_le_three hd.cfg.glob hd.cfg.loc.sigma hd.cfg.loc.isCoreMaxLocal
  exact CFSG.LocalAnalysis.RankThreeTheoremC.pRank_centBase_le_two hRM (P.isPGroup'.to_le hRP)
    cfg.center cfg.quot ((CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hG)

theorem factor_of_nineThree_card {p : ℕ} [Fact p.Prime] {M H N : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1)
    (hKX : ¬ K ≤ d1X0 p M H) (hcov : AGLCovers p H N K)
    (hcore : (primeComplementCore (G := N) p).map N.subtype ≤ M)
    {JN : Subgroup (N ⧸ primeComplementCore (G := N) p)} (h93 : Hyp111NineThree p M N JN)
    (hcard : Nat.card JN ≤ Nat.card K) (hout : Group.IsSolvable (Outer JN)) :
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y := by
  obtain ⟨W, hW, J, φ, -, hWJ, hφs, hJper, hY₀⟩ :=
    exists_perfect_cover hKs hKnab hKp hKX hcov hcore
  haveI := h93.normal
  haveI := hKs
  set C := Subgroup.centralizer (JN : Set (N ⧸ primeComplementCore (G := N) p))
  have hCn : C.Normal := inferInstance
  have hCX : C ≤ d1X0 p M N := by
    intro c hc
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := N) p) c
    exact ⟨n, Subgroup.mem_subgroupOf.mpr ⟨n.2, h93.plusCore_le ⟨n, hc, rfl⟩⟩, rfl⟩
  have hJle : J ≤ JN ⊔ C := le_sup_centralizer_of_isPerfect hJper hout
  have hker : C.subgroupOf J ≤ φ.ker := by
    have hnorm : ((C.subgroupOf J).map φ).Normal := (Subgroup.normal_subgroupOf).map φ hφs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C.subgroupOf J).map φ) with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).mp hbot
    · exact absurd (eq_top_iff.mpr (htop.symm.le.trans (Subgroup.map_mono fun j hj =>
        Subgroup.mem_subgroupOf.mpr (hCX (Subgroup.mem_subgroupOf.mp hj))))) hY₀
  have hrJ : Nat.card K ≤ C.relIndex J := by
    have e1 := Subgroup.index_mul_card (C.subgroupOf J)
    have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv] at e2
    have e3 := Subgroup.card_le_of_le hker
    have hpos : 0 < Nat.card (C.subgroupOf J) := Nat.card_pos
    show Nat.card K ≤ (C.subgroupOf J).index
    by_contra hlt
    push Not at hlt
    have : (C.subgroupOf J).index * Nat.card (C.subgroupOf J) < Nat.card K * Nat.card φ.ker :=
      calc (C.subgroupOf J).index * Nat.card (C.subgroupOf J)
          < Nat.card K * Nat.card (C.subgroupOf J) := Nat.mul_lt_mul_of_pos_right hlt hpos
        _ ≤ Nat.card K * Nat.card φ.ker := Nat.mul_le_mul_left _ e3
    omega
  have hr1 : C.relIndex JN ≤ Nat.card JN := by
    have e := Subgroup.relIndex_mul_card (H := C) (K := JN)
    have hpos : 0 < Nat.card (C ⊓ JN : Subgroup _) := Nat.card_pos
    nlinarith
  have heq : J ⊔ C = JN ⊔ C := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hJle le_sup_right) ?_
    have c1 := Subgroup.relIndex_mul_card (H := C) (K := J ⊔ C)
    have c2 := Subgroup.relIndex_mul_card (H := C) (K := JN ⊔ C)
    rw [inf_of_le_left le_sup_right] at c1 c2
    rw [← c1, ← c2, Subgroup.relIndex_sup_right J C, Subgroup.relIndex_sup_right JN C]
    exact Nat.mul_le_mul_right _ ((hr1.trans hcard).trans hrJ)
  refine factor_of_forall_mul hW hcore fun y => ?_
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := N) p) y
  obtain ⟨m, hm, k, hk, hnk⟩ := h93.factor n n.2
  have hn : n = ⟨m, hm.1⟩ * k := Subtype.ext hnk
  have hk' : QuotientGroup.mk' (primeComplementCore (G := N) p) k ∈ C ⊔ J := by
    rw [sup_comm, heq]; exact Subgroup.mem_sup_left hk
  obtain ⟨c, hc, j, hj, hcj⟩ := Subgroup.mem_sup_of_normal_left.mp hk'
  refine ⟨QuotientGroup.mk' (primeComplementCore (G := N) p) ⟨m, hm.1⟩ * c,
    (d1X0 p M N).mul_mem ⟨⟨m, hm.1⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩ (hCX hc), j, hWJ ▸ hj,
    ?_⟩
  rw [hn, map_mul, ← hcj, mul_assoc]

theorem aglRankTwoFactorAt_of_nineThree {p : ℕ} [Fact p.Prime] {M H B : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKs : IsSimpleGroup K)
    (hKnab : ∃ a b : K, a * b ≠ b * a) (hKp : ∃ x : K, x ≠ 1 ∧ ∃ k : ℕ, x ^ p ^ k = 1)
    (hKX : ¬ K ≤ d1X0 p M H)
    (hat : ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N → AGLCovers p H N K →
      B ≤ T → T ≤ N → T ≤ M → IsPGroup p T →
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) →
      (T = B ∨ Open.pRank p T ≤ 2) →
      (primeComplementCore (G := N) p).map N.subtype ≤ M ∧
      ∃ JN : Subgroup (N ⧸ primeComplementCore (G := N) p), Hyp111NineThree p M N JN ∧
        Nat.card JN ≤ Nat.card K ∧ Group.IsSolvable (Outer JN)) :
    AGLRankTwoFactorAt p M H B K := by
  intro N T hN hNM hBN hcov hBT hTN hTM hT hmax hor
  obtain ⟨hcore, JN, h93, hcard, hout⟩ := hat N T hN hNM hBN hcov hBT hTN hTM hT hmax hor
  exact factor_of_nineThree_card hKs hKnab hKp hKX hcov hcore h93 hcard hout

@[expose] def TwoRestRankTwoNineThree (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (z : H) (Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L : Subgroup G)
    (hRM : R ≤ M), TwoRestG23Config P M H R Rbar z Kbar L →
    ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → centBase M R L hRM ≤ N →
      AGLCovers 3 H N (innerNotQJ 3 H Kbar) → centBase M R L hRM ≤ T → T ≤ N → T ≤ M →
      IsPGroup 3 T → (∀ V : Subgroup G, V ≤ N → IsPGroup 3 V → T ≤ V → V = T) →
      Open.pRank 3 T ≤ 2 →
      (primeComplementCore (G := N) 3).map N.subtype ≤ M ∧
      ∃ JN : Subgroup (N ⧸ primeComplementCore (G := N) 3), Hyp111NineThree 3 M N JN ∧
        Nat.card JN ≤ Nat.card (innerNotQJ 3 H Kbar) ∧ Group.IsSolvable (Outer JN)

theorem twoRestRankTwoFactor_of_nineThree (hk : D1CaseTwoKFacts3 G)
    (h1014 : TwoRestTenFourteen G) (h : TwoRestRankTwoNineThree G) : TwoRestRankTwoFactor G := by
  intro P M H R Rbar z Kbar L hRM cfg
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJ, hKs, hKnab, hKp, -, -⟩ := cfg.kbar_facts hk h1014 hRM
  have hB2 := cfg.pRank_centBase_le_two hRM
  have hat := h P M H R Rbar z Kbar L hRM cfg
  rw [hJ] at hat ⊢
  refine aglRankTwoFactorAt_of_nineThree hKs hKnab hKp cfg.not_le ?_
  intro N T hN hNM hBN hcov hBT hTN hTM hT hmax hor
  refine hat N T hN hNM hBN hcov hBT hTN hTM hT hmax ?_
  rcases hor with rfl | h2
  · exact hB2
  · exact h2

theorem twoRestNineSeventeen_rankTwo_of_nineThree (hk : D1CaseTwoKFacts3 G)
    (h1014 : TwoRestTenFourteen G) (h3 : D1CaseThreeNotKlingen3 G)
    (hother : D1CaseThreeKlingenOther3 G) (hkl : KFactKlingenLocal) (hmod : StmtKlingenModel)
    (h : TwoRestRankTwoNineThree G) :
    TwoRestNineSeventeen G ∧ TwoRestRankTwoFactor G :=
  have h2 := twoRestRankTwoFactor_of_nineThree hk h1014 h
  ⟨twoRestNineSeventeen_of_rankTwo hk h1014 h3 hother hkl hmod h2, h2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
