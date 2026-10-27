module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitTripleBranch
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit

theorem eq_of_commute_of_isCyclic_sylow {H : Type*} [Group H] [Finite H]
    (hcyc : ∀ P : Sylow 2 H, IsCyclic (P : Subgroup H)) {s t : H} (hs : orderOf s = 2)
    (ht : orderOf t = 2) (hst : s * t = t * s) : s = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := (GSLit.isPGroup_two_sup_zpowers hs ht hst).exists_le_sylow
  have hsP : s ∈ (P : Subgroup H) := hP (mem_sup_right (mem_zpowers s))
  have htP : t ∈ (P : Subgroup H) := hP (mem_sup_left (mem_zpowers t))
  have := hcyc P
  have hs' : orderOf (⟨s, hsP⟩ : (P : Subgroup H)) = 2 := by rw [Subgroup.orderOf_mk]; exact hs
  have ht' : orderOf (⟨t, htP⟩ : (P : Subgroup H)) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hcard : Nat.card (zpowers (⟨s, hsP⟩ : (P : Subgroup H))) =
      Nat.card (zpowers (⟨t, htP⟩ : (P : Subgroup H))) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hs', ht']
  have heq := IsCyclic.subgroup_eq_iff_card_eq.mpr hcard
  have htmem : (⟨t, htP⟩ : (P : Subgroup H)) ∈ zpowers (⟨s, hsP⟩ : (P : Subgroup H)) :=
    heq ▸ mem_zpowers _
  rcases UnbalancedGS.DihedralPair.mem_zpowers_eq_one_or_eq hs' htmem with h1 | h1
  · rw [h1, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  · exact (congrArg Subtype.val h1).symm

variable {G : Type*} [Group G] [Finite G]

theorem reach_eq_of_isCyclic_kernel {L : Subgroup G}
    (hcyc : ∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L)))
    {M : Subgroup G} (hM : GSReach L M) : M = L := by
  obtain ⟨-, hR⟩ := hM
  induction hR with
  | refl => rfl
  | @tail M N _ hst ih =>
    obtain ⟨s, t, hC⟩ := hst
    rw [ih] at hC
    have hsK : s ∈ coreActionKernel L :=
      GSLit.mem_coreActionKernel_of_le_centralizer hC.2.2.2.1
    have htK : t ∈ coreActionKernel L := ⟨hC.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.1⟩
    have hst : (⟨s, hsK⟩ : coreActionKernel L) = ⟨t, htK⟩ :=
      eq_of_commute_of_isCyclic_sylow hcyc (by rw [Subgroup.orderOf_mk]; exact hC.1)
        (by rw [Subgroup.orderOf_mk]; exact hC.2.1) (Subtype.ext hC.2.2.1)
    have hst' : s = t := congrArg Subtype.val hst
    subst hst'
    exact GSLit.GSCorr.eq_of_eq_involution hC

theorem gsMaximalComponent_of_isCyclic_kernel {b : G} {L : Subgroup G} (hb : orderOf b = 2)
    (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))))
    (hcyc : ∀ P : Sylow 2 ↥(coreActionKernel L), IsCyclic (P : Subgroup ↥(coreActionKernel L))) :
    GSMaximalComponent L := by
  refine ⟨⟨b, hb, hLb, hL⟩, fun M hM => ?_⟩
  obtain rfl := reach_eq_of_isCyclic_kernel hcyc hM
  exact ⟨MulEquiv.refl _⟩

theorem two_le_pRank_of_small_type {X : Type} [Group X] [Finite X] {x : X} {L : Subgroup X}
    (hLx : L ≤ centralizer ({x} : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))))
    (htype : Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) : 2 ≤ pRank 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : L ⧸ oddCore L ≃* L ⧸ pPrimeCore 2 L :=
    QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two L)
  have hq : IsQuasisimple (L ⧸ pPrimeCore 2 L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLx).1 hL).2.2
  have hA : IsQuasisimple (L ⧸ oddCore L) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e.symm).1 hq
  rcases htype with ⟨⟨e7⟩⟩ | ⟨p, f, hp, hp2, hf, -, hmodel⟩
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inr (Or.inl ⟨e.trans e7⟩))
  · exact UnbalancedGS.small_source_models_force_rank_at_least_two hA
      (Or.inl ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, SectionRank.statedClassicalModel_of_mulEquiv e
        (GSLit.statedClassicalModel_of_lieModel_psl_two hmodel)⟩)

theorem false_of_gsMaximalComponent_small (hH : HarrisInput) (hF : FooteInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {x : X} {L : Subgroup X} (hx : orderOf x = 2)
    (hLx : L ≤ centralizer ({x} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))))
    (hL : GSMaximalComponent L)
    (htype : Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) : False := by
  rcases hF X hnonab hK x hx L hLx hLc hL htype with
    hlie | hrank | ⟨⟨e9⟩, -⟩ | ⟨⟨e10⟩, -⟩ | ⟨⟨e11⟩, -⟩ | ⟨⟨eJ⟩, -⟩
  · exact hU (GSLit.uOutcome_of_oddLieType hlie)
  · obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(coreActionKernel L)) := inferInstance
    rcases GSLit.sylow_cyclic_or_quaternion_of_pRank_eq_one hrank P with hcyc | ⟨r, hr, ⟨eP⟩⟩
    · have hall : ∀ Q : Sylow 2 ↥(coreActionKernel L),
          IsCyclic (Q : Subgroup ↥(coreActionKernel L)) :=
        fun Q => (MulEquiv.isCyclic (Sylow.equiv P Q)).mp hcyc
      rcases htype with ⟨⟨e7⟩⟩ | hpsl
      · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
          alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
        have hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := e7.isSimpleGroup
        obtain ⟨S⟩ : Nonempty (Sylow 2 (L ⧸ pPrimeCore 2 L)) := inferInstance
        have hS8 : Nat.card (S : Subgroup (L ⧸ pPrimeCore 2 L)) = 8 :=
          GSLit.card_sylow_two_of_card_eq_2520
            (by rw [Nat.card_congr e7.toEquiv, GSLit.card_alternating_seven]) S
        rcases hHSF X hnonab x hx L hLx hLc hs (GSLit.pRank_two_of_mulEquiv_alternating_seven e7)
            ⟨S, hS8⟩ hall with hlie | ⟨⟨e6⟩, -⟩
        · exact hU (GSLit.uOutcome_of_oddLieType hlie)
        · have h67 := Nat.card_congr (e6.symm.trans e7).toEquiv
          rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at h67
          norm_num [Nat.factorial] at h67
      · exact hH X hnonab hK hz hU ⟨x, L, hx, hLx, hLc, hL, hpsl, hall⟩
    · exact GSLit.false_of_quaternion_kernel hCI hnonab hz hU hx hLx hLc
        (two_le_pRank_of_small_type hLx hLc htype) hrank P hr eP
  · have h9 := GSLit.mod_four_eq_three_of_mulEquiv_alternating hnonab (by norm_num) e9 hz
    norm_num at h9
  · have h10 := GSLit.mod_four_eq_three_of_mulEquiv_alternating hnonab (by norm_num) e10 hz
    norm_num at h10
  · exact hU (GSLit.uOutcome_of_mulEquiv_alternating_eleven e11)
  · exact GSLit.false_of_mulEquiv_j2 eJ hz

theorem isSimpleGroup_of_lieModel_psl_two {X : Type} [Group X] {p f : ℕ}
    (hL : Blueprint.LieModel X .PSL 2 p f) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL

theorem fusionZStar_eq_pPrimeCore_of_simple {Y : Type*} [Group Y]
    (hs : IsSimpleGroup (Y ⧸ pPrimeCore 2 Y)) (hne : Open.fusionZStar Y ≠ ⊤) :
    Open.fusionZStar Y = pPrimeCore 2 Y := by
  have hO := UnbalancingLocal.fusionOddCore_eq_pPrimeCore Y
  let e : Y ⧸ Open.fusionOddCore Y ≃* Y ⧸ pPrimeCore 2 Y := QuotientGroup.quotientMulEquivOfEq hO
  have he : ∀ y : Y, e (QuotientGroup.mk' (Open.fusionOddCore Y) y) = (y : Y ⧸ pPrimeCore 2 Y) :=
    fun y => QuotientGroup.quotientMulEquivOfEq_mk hO y
  have hcen : ∀ y : Y, y ∈ Open.fusionZStar Y ↔
      (y : Y ⧸ pPrimeCore 2 Y) ∈ center (Y ⧸ pPrimeCore 2 Y) := by
    intro y
    show QuotientGroup.mk' (Open.fusionOddCore Y) y ∈ center _ ↔ _
    constructor
    · intro h1
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := e.surjective g
      have h2 := congrArg e (mem_center_iff.mp h1 g')
      rwa [map_mul, map_mul, he] at h2
    · intro h1
      rw [mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul, he]
      exact mem_center_iff.mp h1 (e g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Y ⧸ pPrimeCore 2 Y)) with h | h
  · ext y
    rw [hcen, h, mem_bot, QuotientGroup.eq_one_iff]
  · exfalso
    apply hne
    ext y
    simp only [mem_top, iff_true]
    rw [hcen, h]
    exact mem_top _

theorem false_of_psl34_of_psl_two {J : Type} [Group J] [Finite J] {p f : ℕ}
    (h34 : Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2) (hp2 : p ≠ 2)
    (h2 : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f) : False := by
  have h20160 := (PSL3Four.excludes_alternating_models_stated.{0} _
    (GSLit.statedClassicalModel_of_lieModel_psl_three h34)).1
  have hne : Open.fusionZStar J ≠ ⊤ := by
    intro htop
    have h1 : Nat.card (J ⧸ Open.fusionZStar J) = 1 := by
      rw [htop]
      exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, inferInstance⟩
    omega
  have hZ := fusionZStar_eq_pPrimeCore_of_simple (isSimpleGroup_of_lieModel_psl_two h2) hne
  have hcard1 : Nat.card (J ⧸ pPrimeCore 2 J) = 20160 := by
    rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hZ).toEquiv]
    exact h20160
  obtain ⟨⟨hp, hf, -, -, -⟩, F, _, _, hF, ⟨e2⟩⟩ := GSLit.statedClassicalModel_of_lieModel_psl_two h2
  have hcard2 := GorensteinWalter.psl2_card_formula F ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩
  rw [← Nat.card_congr
    ((e2.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).toEquiv),
    hcard1, hF] at hcard2
  set q := p ^ f with hq
  have key : q * (q ^ 2 - 1) = 40320 ∨ q * (q ^ 2 - 1) = 40321 := by omega
  rcases le_or_gt q 34 with h | h
  · have hle : q * (q ^ 2 - 1) ≤ 34 * (34 ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    norm_num at hle
    omega
  · have hle : 35 * (35 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    norm_num at hle
    omega

theorem exists_maximal_he_or_l34 (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGF : GloballyFirstRankTwoInput) (hB : TheoremBBoundedInput) (hH : HarrisInput)
    (hF : FooteInput) (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (htriple : ∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J) :
    ∃ (a x : X) (J : Subgroup X), GSMaximalUnbalancingTriple a x J ∧
      (∀ (c v : X) (K : Subgroup X), GSUnbalancingTriple c v K →
        (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index) ∧
      (Nonempty (J ⧸ pPrimeCore 2 J ≃* Blueprint.NativeSporadic.He) ∨
        (Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2 ∧ GSMaximalComponent J)) := by
  obtain ⟨a, x, J, hJ, hbound⟩ :=
    GSLit.exists_maximal_unbalancing_triple_bounded hTB hSA hGF hnonab hK hz hU htriple
  refine ⟨a, x, J, hJ, hbound, ?_⟩
  have ha : orderOf a = 2 := hJ.1.1
  have hJa : J ≤ centralizer ({a} : Set X) := hJ.1.2.2.2.1
  have hJc : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))) := hJ.1.2.2.2.2.1
  rcases hTB X hnonab hK hz hU a x J hJ.1 with ⟨n, hodd, hn, he⟩ | hsmall | hbig
  · exact absurd ⟨a, J, n, ha, hodd, hn, hJa, hJc, he⟩ (hSA X hnonab hK hz hU)
  · exfalso
    rcases hB X hnonab hK hz hU a x J hJ hbound (hsmall.imp id Or.inl) with
      ⟨-, b, L, ρ, e, hb, hLb, hL, hρ, hρ2, he, hLie, hbK, hP⟩ | ⟨hiso, hcentral⟩
    · refine (hH X hnonab hK hz hU) ⟨b, L, hb, hLb, hL,
        GSLit.gsMaximalComponent_of_cyclic_kernel hb hLb hL hP,
        ⟨ρ, 2 * e, hρ, hρ2, by omega, ?_, hLie⟩, GSLit.isCyclic_sylow_of_eq_zpowers hbK hP⟩
      have h3 : 3 ≤ ρ := by have := hρ.two_le; omega
      calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ ρ ^ 2 := Nat.pow_le_pow_left h3 2
        _ ≤ ρ ^ (2 * e) := Nat.pow_le_pow_right hρ.pos (by omega)
    · exact false_of_gsMaximalComponent_small hH hF hHSF hCI hnonab hK hz hU ha hJa hJc
        (GSLit.gsMaximalComponent_of_B2 ha hJa hJc hiso hcentral) hsmall
  · rcases hbig with hHe | h34
    · exact Or.inl hHe
    · refine Or.inr ⟨h34, ?_⟩
      rcases hB X hnonab hK hz hU a x J hJ hbound (Or.inr (Or.inr h34)) with
        ⟨⟨p, f, -, hp2, -, hpsl⟩, -⟩ | ⟨hiso, hcentral⟩
      · exact (false_of_psl34_of_psl_two h34 hp2 hpsl).elim
      · exact GSLit.gsMaximalComponent_of_B2 ha hJa hJc hiso hcentral

end CFSG.ComponentClassification.GrSLit
