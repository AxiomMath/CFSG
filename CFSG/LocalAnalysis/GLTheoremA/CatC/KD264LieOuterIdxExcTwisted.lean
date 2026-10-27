module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterExcTwisted
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdx
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSRT
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFixed
public import CFSG.LieType.SeitzGeneration.HyperCoverE6
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenRee
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreTight
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.ReeTransport
public import CFSG.HardMathSupport.Lang.E27.TwistedE6Field

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


private theorem outerIdxAt_tits {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {hv : TauCeti.LieTypeIndex.tits.Valid} :
    OuterIdxAt p .tits (CFSG.LieType.SeitzGeneration.Cat ⟨.tits, hv⟩) := by
  haveI : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨.tits, hv⟩) :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.LieType.SeitzGeneration.card_cat_tits hv]; norm_num)
  refine outerIdxAt_of_idxCoreAt hp ?_
  intro x hxp hxout
  exfalso
  haveI : Fact p.Prime := ⟨hp⟩
  have hmodel : CFSG.Blueprint.ReeTitsModel
      (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩) .Tits 2 1 :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_tits
      (S := CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩)
      ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨h2, -⟩ :=
    CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ 2 1 hmodel
  have hpow : (QuotientGroup.mk x : Outer (CFSG.LieType.SeitzGeneration.Cat
      ⟨TauCeti.LieTypeIndex.tits, hv⟩)) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hxp, QuotientGroup.mk_one]
  have hdiv1 : orderOf (QuotientGroup.mk x : Outer
      (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩)) ∣ p :=
    orderOf_dvd_of_pow_eq_one hpow
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hdiv2 : orderOf (QuotientGroup.mk x : Outer
      (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩)) ∣ 2 ^ n := by
    rw [← hn]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime p (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_right.2 (hp.odd_of_ne_two hp2))
  have hone : orderOf (QuotientGroup.mk x : Outer
      (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩)) = 1 :=
    Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hdiv1 hdiv2)
  have hxinner : x ∈ inner (CFSG.LieType.SeitzGeneration.Cat
      ⟨TauCeti.LieTypeIndex.tits, hv⟩) := by
    rw [← QuotientGroup.eq_one_iff, orderOf_eq_one_iff.1 hone]
  exact hxout (inner_le_innAutDerived _ hxinner)

private theorem outerIdxAt_suzukiGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : ℕ} (ha : 1 ≤ a) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ (2 * a + 1))
    (hnExc : ¬ outerIdxExc p (.suzuki a))
    (hpdvd : p ∣ Nat.card (CFSG.Blueprint.suzukiGroup a F)) :
    OuterIdxAt p (.suzuki a) (CFSG.Blueprint.suzukiGroup a F) := by
  refine outerIdxAt_of_idxCoreAt hp ?_
  intro x hxp hxout
  haveI : Fact p.Prime := ⟨hp⟩
  have hxinner : x ∉ inner (CFSG.Blueprint.suzukiGroup a F) :=
    fun hx => hxout (inner_le_innAutDerived _ hx)
  have hx1 : x ≠ 1 := fun h1 => hxout (by rw [h1]; exact one_mem _)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  obtain ⟨σ, h, b, k, _, _, _, hbp, hkc, hconj, ⟨eH⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha F hF p hp hp2 x hxord hxinner
  set δ := szFieldAut a F σ with hδ
  have hconj' : MulAut.congr (MulAut.conj h : CFSG.Blueprint.suzukiGroup a F ≃*
      CFSG.Blueprint.suzukiGroup a F) x = δ := by
    rw [← hconj]
    ext z
    simp [MulAut.congr_apply, MulAut.mul_apply]
  have hfixmap : fixSubgroup δ = (fixSubgroup x).map (MulAut.conj h).toMonoidHom := by
    rw [← hconj']
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr (MulAut.conj h) x
  obtain ⟨y, hy, hyord⟩ := exists_orderOf_eq_prime_mem_fixSubgroup hp x hxp hpdvd
  have hpfixx : p ∣ Nat.card (fixSubgroup x) := by
    have hord : p = orderOf (⟨y, hy⟩ : fixSubgroup x) := by
      rw [Subgroup.orderOf_mk, hyord]
    rw [hord]
    exact orderOf_dvd_natCard _
  have hb1 : 1 ≤ b := by
    by_contra hb
    have hb0 : b = 0 := by omega
    subst hb0
    have hcardk : Nat.card k = 2 := by simpa using hkc
    have h20 : Nat.card (CFSG.Blueprint.suzukiGroup 0 k) = 20 := by
      rw [CFSG.LieType.Ree.suzuki_order hcardk]; norm_num
    have hpdvd_eq : Nat.card (fixSubgroup δ) =
        Nat.card (CFSG.Blueprint.suzukiGroup 0 k) := Nat.card_congr eH.toEquiv
    have hdvd20 : p ∣ 20 := by
      have hfixδ : p ∣ Nat.card (fixSubgroup δ) := by
        rw [hfixmap, Subgroup.card_map_of_injective (MulAut.conj h).injective]
        exact hpfixx
      rw [hpdvd_eq, h20] at hfixδ
      exact hfixδ
    have hp5 : p = 5 := by
      have h1 : p ∣ 2 ^ 2 * 5 := by simpa using hdvd20
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow h1)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h1
    have ha2 : a = 2 := by omega
    exact hnExc (by simpa [outerIdxExc] using ⟨hp5, by rw [ha2]⟩)
  have hqk : CFSG.IsQuasisimple (CFSG.Blueprint.suzukiGroup b k) :=
    CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.isQuasisimple_suzukiGroup hb1 hkc
  let eX : fixSubgroup x ≃* CFSG.Blueprint.suzukiGroup b k :=
    ((Subgroup.equivMapOfInjective (fixSubgroup x) (MulAut.conj h).toMonoidHom
        (MulAut.conj h).injective).trans
      (MulEquiv.subgroupCongr hfixmap.symm)).trans eH
  have hq : CFSG.IsQuasisimple (fixSubgroup x) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hqk
  let hv' := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzuki_valid hb1
  obtain ⟨eCat⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_suzukiGroup_equiv_cat hb1 hkc
  have hZ : Subgroup.center (fixSubgroup x) = ⊥ :=
    CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv eX
      (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot hb1 hkc)
  refine ⟨fixSubgroup x, le_rfl, ?_, hq, hpfixx, ?_⟩
  · intro f hf t ht
    exact mul_mem (mul_mem hf ht) (inv_mem hf)
  · refine ⟨.lie ⟨.suzuki b, hv'⟩, ⟨?_⟩, ?_⟩
    · exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
        (QuotientGroup.quotientBot.trans (eX.trans eCat))
    · refine Or.inl ⟨trivial, ?_⟩
      show (2 ^ (2 * b + 1)) ^ p = 2 ^ (2 * a + 1)
      rw [← pow_mul, hbp]

private theorem outerIdxAt_suzuki {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m : ℕ} (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (hnExc : ¬ outerIdxExc p (.suzuki m))
    (hpdvd : p ∣ Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.suzuki m, hv⟩)) :
    OuterIdxAt p (.suzuki m) (CFSG.LieType.SeitzGeneration.Cat ⟨.suzuki m, hv⟩) := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e0⟩⟩ :=
    CFSG.LieType.SeitzGeneration.suzukiModel_cat hv
  have ham : m = a := by omega
  subst m
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF]
  have hpdvd' : p ∣ Nat.card (CFSG.Blueprint.suzukiGroup a F) := by
    rw [← Nat.card_congr e0.toEquiv]
    exact hpdvd
  exact outerIdxAt_of_mulEquiv hp e0.symm
    (outerIdxAt_suzukiGroup hp hp2 ha hF' hnExc hpdvd')


private theorem outerIdxAt_reeG2Model {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1))
    (hpdvd : p ∣ Nat.card (ReeTag.G2.reeGamma K a)) :
    OuterIdxAt p (.reeG2 a) (ReeTag.G2.reeGamma K a) := by
  refine outerIdxAt_of_idxCoreAt hp ?_
  intro α hαp hαout
  haveI : Fact p.Prime := ⟨hp⟩
  have hαinner : α ∉ inner (ReeTag.G2.reeGamma K a) :=
    fun hα => hαout (inner_le_innAutDerived _ hα)
  obtain ⟨hpdvdm, δ, σ, hσp, hconj, hkcard, hfixed⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hp hp2
      α hαp hαinner
  set b : ℕ := ((2 * a + 1) / p - 1) / 2 with hbdef
  have hd : (2 * b + 1) * p = 2 * a + 1 := by
    have hdvd : p ∣ 2 * a + 1 := hpdvdm
    have hodd : Odd ((2 * a + 1) / p) := by
      apply Nat.not_even_iff_odd.1
      intro he
      have hoddprod : Odd (p * ((2 * a + 1) / p)) := by
        rw [mul_comm, Nat.div_mul_cancel hdvd]
        exact odd_two_mul_add_one a
      obtain ⟨c, hc⟩ := he
      have hevenprod : Even (p * ((2 * a + 1) / p)) := ⟨p * c, by rw [hc]; ring⟩
      exact Nat.not_even_iff_odd.2 hoddprod hevenprod
    obtain ⟨c, hc⟩ := hodd
    have hbval : b = c := by
      rw [hbdef, hc]
      omega
    have h2b : 2 * b + 1 = (2 * a + 1) / p := by rw [hbval, hc]
    have hdmul : ((2 * a + 1) / p) * p = 2 * a + 1 := Nat.div_mul_cancel hdvd
    rw [h2b, hdmul]
  have hbEq : 2 * b + 1 = (2 * a + 1) / p := by
    rw [← hd, Nat.mul_div_cancel _ hp.pos]
  have hbcard : Nat.card (fixSubfield σ) = 3 ^ (2 * b + 1) := by
    rw [hbEq]; exact hkcard
  let φ : MulAut (ReeTag.G2.reeGamma K a) := ReeTag.G2.reeGammaFieldAut K a σ
  let J : Subgroup (ReeTag.G2.reeGamma K a) := φ.toMonoidHom.eqLocus (MonoidHom.id _)
  have hJfix : J = fixSubgroup φ := rfl
  have hφp : orderOf φ = p := by
    change orderOf (ReeTag.G2.reeGammaFieldAut K a σ) = p
    rw [← hconj]
    exact (MulEquiv.orderOf_eq (MulAut.conj δ) α).trans (orderOf_eq_prime hαp (by
      intro h1
      exact hαinner (by rw [h1]; exact one_mem _)))
  have hφpow : φ ^ p = 1 := by rw [← hφp]; exact pow_orderOf_eq_one φ
  obtain ⟨y, hy, hyord⟩ := exists_orderOf_eq_prime_mem_fixSubgroup hp φ hφpow hpdvd
  have hdvdJ : p ∣ Nat.card J := by
    have hord : p = orderOf (⟨y, hy⟩ : fixSubgroup φ) := by
      rw [Subgroup.orderOf_mk, hyord]
    rw [hJfix, hord]
    exact orderOf_dvd_natCard _
  let T : Subgroup (ReeTag.G2.reeGamma K a) := (commutator J).map J.subtype
  let eC : J ≃* ReeTag.G2.reeGamma (fixSubfield σ) b :=
    (((J).equivMapOfInjective (ReeTag.G2.reeGamma K a).subtype
        (ReeTag.G2.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixed)).trans
      ((ReeTag.G2.reeGamma (fixSubfield σ) b).equivMapOfInjective _
        (baseChangeGL_injective (τ := ReeTag.G2.tag) (fixSubfield σ).subtype)).symm
  let eT : commutator J ≃* commutator (ReeTag.G2.reeGamma (fixSubfield σ) b) :=
    ((commutator J).equivMapOfInjective eC.toMonoidHom eC.injective).trans
      (MulEquiv.subgroupCongr
        (CFSG.ComponentClassification.CatalogueBSmallRee.map_commutator_mulEquiv eC))
  let eTT : commutator (ReeTag.G2.reeGamma (fixSubfield σ) b) ≃* T :=
    eT.symm.trans ((commutator J).equivMapOfInjective J.subtype J.subtype_injective)
  have hTeq : Nat.card T = Nat.card (commutator (ReeTag.G2.reeGamma (fixSubfield σ) b)) :=
    Nat.card_congr eTT.symm.toEquiv
  have hJeq : Nat.card J = Nat.card (ReeTag.G2.reeGamma (fixSubfield σ) b) :=
    Nat.card_congr eC.toEquiv
  obtain ⟨hs, hnc, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components
      b (fixSubfield σ) hbcard
  haveI : IsSimpleGroup (commutator (ReeTag.G2.reeGamma (fixSubfield σ) b)) := hs
  have hqk : CFSG.IsQuasisimple (commutator (ReeTag.G2.reeGamma (fixSubfield σ) b)) :=
    CFSG.ClassicalInvolution.Asc77.T3Core.isQuasisimple_of_simple_nonabelian hnc
  have hTq : CFSG.IsQuasisimple T :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eTT hqk
  have hTle : T ≤ fixSubgroup φ := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hTn : ∀ f ∈ fixSubgroup φ, ∀ t ∈ T, f * t * f⁻¹ ∈ T := by
    rintro f hf _ ⟨t, ht, rfl⟩
    refine ⟨⟨f, hf⟩ * t * ⟨f, hf⟩⁻¹,
      (inferInstance : (commutator J).Normal).conj_mem t ht ⟨f, hf⟩, ?_⟩
    simp
  haveI : IsSimpleGroup T := eTT.symm.isSimpleGroup
  have hncT : ∃ u v : T, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := hnc
    exact ⟨eTT u, eTT v, fun h => huv (eTT.injective (by simpa using h))⟩
  have hZT : Subgroup.center T = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := hncT
      exact huv (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top v) u)
  have hTp : p ∣ Nat.card T := by
    rw [hTeq]
    rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · rw [hb0] at hbcard ⊢
      obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
      obtain ⟨-, -, -, -, hzero, -⟩ :=
        CFSG.ComponentClassification.CatalogueBSmallRee.small_Ree_whole_group_p_components
          0 (fixSubfield σ) hbcard
      obtain ⟨-, h504, -⟩ := hzero rfl w₀ hw₀
      rw [h504]
      have hJ1512 : Nat.card J = 1512 := by
        rw [hb0] at hJeq
        rw [hJeq, CFSG.ComponentClassification.LiteratureLocal.G2_card_reeGamma 0 hbcard]
        norm_num
      rw [hJ1512] at hdvdJ
      have hp7 : p = 7 := by
        have h : p ∣ 2 ^ 3 * 3 ^ 3 * 7 := by
          rwa [show (1512 : ℕ) = 2 ^ 3 * 3 ^ 3 * 7 by norm_num] at hdvdJ
        rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
              (hp.dvd_of_dvd_pow h)) hp2
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
              (hp.dvd_of_dvd_pow h)) hp3
        · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).1 h
      rw [hp7]; norm_num
    · have htop : commutator (ReeTag.G2.reeGamma (fixSubfield σ) b) = ⊤ :=
        (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hb1
          (fixSubfield σ) hbcard).1
      rw [htop, Subgroup.card_top, ← hJeq]
      exact hdvdJ
  have hcoreφ : IdxCoreAt p (.reeG2 a) φ := by
    refine ⟨T, hTle, hTn, hTq, hTp, ?_⟩
    by_cases hb0 : b = 0
    · rw [hb0] at hbcard hd eTT hTeq hJeq
      let q8 : TauCeti.PrimePower := ⟨2, 3, Nat.prime_two, by norm_num⟩
      have hv8 : (TauCeti.LieTypeIndex.A 1 q8).Valid := by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        simp only [TauCeti.PrimePower.card_def, q8]
        norm_num
      obtain ⟨-, -, -, ⟨e⟩, -, -⟩ :=
        CFSG.ComponentClassification.LiteratureLocal.G2_reeGamma_zero_structure hbcard
      have hTcat : Nonempty (T ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q8, hv8⟩).Group) :=
        ⟨eTT.symm.trans (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL
          1 q8 hv8).symm)⟩
      obtain ⟨eTcat⟩ := hTcat
      refine ⟨.lie ⟨.A 1 q8, hv8⟩, ⟨?_⟩, ?_⟩
      · exact (QuotientGroup.quotientMulEquivOfEq hZT).trans
          (QuotientGroup.quotientBot.trans eTcat)
      · have hp_eq : p = 2 * a + 1 := by omega
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
        exact ⟨⟨q8, rfl, by norm_num [q8]⟩, ⟨a, rfl⟩, by rw [hp_eq]; rfl⟩
    · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.2 hb0
      let hv' := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SuzukiReeTits.reeG2_valid hb1
      obtain ⟨eCat⟩ :=
        SuzukiReeTits.nonempty_reeGamma_equiv_catalog b hv' (fixSubfield σ) hbcard
      have htop : commutator (ReeTag.G2.reeGamma (fixSubfield σ) b) = ⊤ :=
        (CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple hb1
          (fixSubfield σ) hbcard).1
      have hTcat : Nonempty (T ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 b, hv'⟩).Group) :=
        ⟨eTT.symm.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) |>.trans eCat⟩
      obtain ⟨eTcat⟩ := hTcat
      refine ⟨.lie ⟨.reeG2 b, hv'⟩, ⟨?_⟩, ?_⟩
      · exact (QuotientGroup.quotientMulEquivOfEq hZT).trans
          (QuotientGroup.quotientBot.trans eTcat)
      · refine Or.inl ⟨trivial, ?_⟩
        show (3 ^ (2 * b + 1)) ^ p = 3 ^ (2 * a + 1)
        rw [← pow_mul, hd]
  exact idxCoreAt_of_conj hcoreφ δ hconj

private theorem outerIdxAt_reeG2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid)
    (hpdvd : p ∣ Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 m, hv⟩)) :
    OuterIdxAt p (.reeG2 m) (CFSG.LieType.SeitzGeneration.Cat ⟨.reeG2 m, hv⟩) := by
  obtain ⟨X, _, _, _, hX, ⟨e0⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat_G2 hv
  have hm1 : 1 ≤ m := by
    have h := ((TauCeti.LieTypeIndex.valid_iff (.reeG2 m)).1 hv).1
    simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hpdvd' : p ∣ Nat.card (ReeTag.G2.reeGamma X m) := by
    rw [← Nat.card_congr e0.toEquiv]
    exact hpdvd
  exact outerIdxAt_of_mulEquiv hp e0.symm
    (outerIdxAt_reeG2Model hp hp2 hp3 hm1 hX hpdvd')


private theorem outerIdxAt_reeF4Model {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hpdvd : p ∣ Nat.card (ReeTag.F4.reeGamma K a)) :
    OuterIdxAt p (.reeF4 a) (ReeTag.F4.reeGamma K a) := by
  refine outerIdxAt_of_idxCoreAt hp ?_
  intro α hαp hαout
  haveI : Fact p.Prime := ⟨hp⟩
  have hαinner : α ∉ inner (ReeTag.F4.reeGamma K a) :=
    fun hα => hαout (inner_le_innAutDerived _ hα)
  have hα1 : α ≠ 1 := fun h1 => hαout (by rw [h1]; exact one_mem _)
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_inner_or_field ha hK hp hαp hα1 with
    ⟨y, rfl, hy, hy1⟩ | ⟨σ, g, hσ, hαeq⟩
  · exact absurd ⟨y, rfl⟩ hαinner
  · let φ : MulAut (ReeTag.F4.reeGamma K a) := ReeTag.F4.reeGammaFieldAut K a σ
    have hφp : orderOf φ = p := by
      change orderOf (ReeTag.F4.reeGammaFieldAut K a σ) = p
      have hconj : (MulAut.conj (MulAut.conj g) : MulAut
          (MulAut (ReeTag.F4.reeGamma K a))) φ = α := by
        rw [hαeq]
        rfl
      calc orderOf φ = orderOf ((MulAut.conj (MulAut.conj g)) φ) :=
            (MulEquiv.orderOf_eq (MulAut.conj (MulAut.conj g)) φ).symm
        _ = orderOf α := by rw [hconj]
        _ = p := hαord
    have hφpow : φ ^ p = 1 := by rw [← hφp]; exact pow_orderOf_eq_one φ
    obtain ⟨b, hbpow, hkcard, hfixed⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.largeRee_fixed_data_of_odd hK hp hp2 σ hσ
    let J : Subgroup (ReeTag.F4.reeGamma K a) := φ.toMonoidHom.eqLocus (MonoidHom.id _)
    have hJfix : J = fixSubgroup φ := rfl
    obtain ⟨y, hy, hyord⟩ := exists_orderOf_eq_prime_mem_fixSubgroup hp φ hφpow hpdvd
    have hdvdJ : p ∣ Nat.card J := by
      have hord : p = orderOf (⟨y, hy⟩ : fixSubgroup φ) := by
        rw [Subgroup.orderOf_mk, hyord]
      rw [hJfix, hord]
      exact orderOf_dvd_natCard _
    let T : Subgroup (ReeTag.F4.reeGamma K a) := (commutator J).map J.subtype
    let eC : J ≃* ReeTag.F4.reeGamma (fixSubfield σ) b :=
      (((J).equivMapOfInjective (ReeTag.F4.reeGamma K a).subtype
          (ReeTag.F4.reeGamma K a).subtype_injective).trans
        (MulEquiv.subgroupCongr hfixed)).trans
        ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
          (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm
    let eT : commutator J ≃* commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) :=
      ((commutator J).equivMapOfInjective eC.toMonoidHom eC.injective).trans
        (MulEquiv.subgroupCongr
          (CFSG.ComponentClassification.CatalogueBSmallRee.map_commutator_mulEquiv eC))
    let eTT : commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) ≃* T :=
      eT.symm.trans ((commutator J).equivMapOfInjective J.subtype J.subtype_injective)
    have hTeq : Nat.card T =
        Nat.card (commutator (ReeTag.F4.reeGamma (fixSubfield σ) b)) :=
      Nat.card_congr eTT.symm.toEquiv
    have hJeq : Nat.card J = Nat.card (ReeTag.F4.reeGamma (fixSubfield σ) b) :=
      Nat.card_congr eC.toEquiv
    have hTq : CFSG.IsQuasisimple T :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eTT
        (isQuasisimple_commutator_reeGamma hkcard)
    have hTle : T ≤ fixSubgroup φ := by
      rintro _ ⟨t, -, rfl⟩
      exact t.2
    have hTn : ∀ f ∈ fixSubgroup φ, ∀ t ∈ T, f * t * f⁻¹ ∈ T := by
      rintro f hf _ ⟨t, ht, rfl⟩
      refine ⟨⟨f, hf⟩ * t * ⟨f, hf⟩⁻¹,
        (inferInstance : (commutator J).Normal).conj_mem t ht ⟨f, hf⟩, ?_⟩
      simp
    have hTp : p ∣ Nat.card T := by
      rw [hTeq]
      rcases Nat.eq_zero_or_pos b with hb0 | hb1
      · rw [hb0] at hkcard ⊢
        have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
        have hidx : (commutator (ReeTag.F4.reeGamma (fixSubfield σ) 0)).index ≤ 2 := by
          have hmap : (commutator (ReeTag.F4.reeGamma (fixSubfield σ) 0)).map
              (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm.toMonoidHom =
              commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0) := by
            rw [commutator_def, Subgroup.map_commutator,
              Subgroup.map_top_of_surjective _
                (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm.surjective,
              ← commutator_def]
          have h1 : ((commutator (ReeTag.F4.reeGamma (fixSubfield σ) 0)).map
              (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm.toMonoidHom).index =
              (commutator (ReeTag.F4.reeGamma (fixSubfield σ) 0)).index := by
            rw [Subgroup.index_map_of_injective _
              (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm.injective,
              MonoidHom.range_eq_top.mpr
                (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm.surjective,
              Subgroup.index_top, mul_one]
          rw [← h1, hmap]
          exact CFSG.ComponentClassification.ExcSelector.index_commutator_reeFixed_tits_le hk2
        have hdvdΓ : p ∣ Nat.card (ReeTag.F4.reeGamma (fixSubfield σ) 0) := by
          rw [hb0] at hJeq
          rw [← hJeq]; exact hdvdJ
        have hmul := Subgroup.card_mul_index
          (commutator (ReeTag.F4.reeGamma (fixSubfield σ) 0))
        rw [← hmul] at hdvdΓ
        rcases (Nat.Prime.dvd_mul hp).1 hdvdΓ with h | h
        · exact h
        · have hpos : 0 < (commutator (ReeTag.F4.reeGamma (fixSubfield σ) 0)).index :=
            Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := commutator
              (ReeTag.F4.reeGamma (fixSubfield σ) 0)))
          have hle : p ≤ (commutator (ReeTag.F4.reeGamma (fixSubfield σ) 0)).index :=
            Nat.le_of_dvd hpos h
          have hp3 : 3 ≤ p := by have := hp.two_le; omega
          omega
      · have htop : commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊤ :=
          ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb1 hkcard
        rw [htop, Subgroup.card_top, ← hJeq]
        exact hdvdJ
    have hcoreφ : IdxCoreAt p (.reeF4 a) φ := by
      refine ⟨T, hTle, hTn, hTq, hTp, ?_⟩
      by_cases hb0 : b = 0
      · rw [hb0] at hkcard eTT
        have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
        obtain ⟨hs, hnc, ⟨e⟩⟩ :=
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.commutator_reeGamma_F4_zero_data hk2
        haveI : IsSimpleGroup (commutator (ReeTag.F4.reeGamma (fixSubfield σ) 0)) := hs
        haveI : IsSimpleGroup T := eTT.symm.isSimpleGroup
        have hncT : ∃ u v : T, u * v ≠ v * u := by
          obtain ⟨u, v, huv⟩ := hnc
          exact ⟨eTT u, eTT v, fun h => huv (eTT.injective (by simpa using h))⟩
        have hZT : Subgroup.center T = ⊥ := by
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
          · exact h
          · exfalso
            obtain ⟨u, v, huv⟩ := hncT
            exact huv (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top v) u)
        have hvT : (TauCeti.LieTypeIndex.tits).Valid := tits_valid
        have hTcat : Nonempty (T ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hvT⟩).Group) :=
          ⟨eTT.symm.trans e⟩
        obtain ⟨eTcat⟩ := hTcat
        refine ⟨.lie ⟨.tits, hvT⟩, ⟨?_⟩, ?_⟩
        · exact (QuotientGroup.quotientMulEquivOfEq hZT).trans
            (QuotientGroup.quotientBot.trans eTcat)
        · have hp_eq : p = 2 * a + 1 := by
            rw [hb0] at hbpow
            omega
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          exact ⟨rfl, ⟨a, rfl⟩, by rw [hp_eq]; rfl⟩
      · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.2 hb0
        let hv' := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.reeF4_valid hb1
        obtain ⟨eCat⟩ :=
          CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeGamma_equiv_cat_of_card
            hb1 hv' hkcard
        haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.reeF4 b, hv'⟩).Group :=
          (CFSG.LieType.SeitzGeneration.finite_isSimpleGroup_cat_reeF4 hv').2
        have htop : commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊤ :=
          ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb1 hkcard
        have hTcat : Nonempty (T ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 b, hv'⟩).Group) :=
          ⟨eTT.symm.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv) |>.trans
            eCat.symm⟩
        obtain ⟨eTcat⟩ := hTcat
        haveI : IsSimpleGroup T := eTcat.isSimpleGroup
        have hncT : ∃ u v : T, u * v ≠ v * u := by
          by_contra h
          push Not at h
          have hcom : ∀ u v : T, u * v = v * u := fun u v => h u v
          haveI : IsMulCommutative T := ⟨⟨hcom⟩⟩
          haveI : IsMulCommutative (T ⧸ Subgroup.center T) := inferInstance
          obtain ⟨u, v, huv⟩ := hTq.2.2
          exact huv (mul_comm u v)
        have hZT : Subgroup.center T = ⊥ := by
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
          · exact h
          · exfalso
            obtain ⟨u, v, huv⟩ := hncT
            exact huv (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top v) u)
        refine ⟨.lie ⟨.reeF4 b, hv'⟩, ⟨?_⟩, ?_⟩
        · exact (QuotientGroup.quotientMulEquivOfEq hZT).trans
            (QuotientGroup.quotientBot.trans eTcat)
        · refine Or.inl ⟨trivial, ?_⟩
          show (2 ^ (2 * b + 1)) ^ p = 2 ^ (2 * a + 1)
          rw [← pow_mul, hbpow]
    have hconj' : (MulAut.conj g)⁻¹ * α * (MulAut.conj g) = φ := by
      change (MulAut.conj g)⁻¹ * α * (MulAut.conj g) =
        ReeTag.F4.reeGammaFieldAut K a σ
      rw [hαeq]
      group
    exact idxCoreAt_of_conj hcoreφ (MulAut.conj g)⁻¹ hconj'

private theorem outerIdxAt_reeF4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    (hpdvd : p ∣ Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.reeF4 m, hv⟩)) :
    OuterIdxAt p (.reeF4 m) (CFSG.LieType.SeitzGeneration.Cat ⟨.reeF4 m, hv⟩) := by
  obtain ⟨X, _, _, _, hm1, hX, -, ⟨e0⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  have hpdvd' : p ∣ Nat.card (ReeTag.F4.reeGamma X m) := by
    rw [← Nat.card_congr e0.toEquiv]
    exact hpdvd
  exact outerIdxAt_of_mulEquiv hp e0.symm
    (outerIdxAt_reeF4Model hp hp2 hm1 hX hpdvd')

private theorem outerIdxAt_twistedE6Model {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = q.card ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q.card)
    (hpdvd : p ∣ Nat.card (twistedE6RootGroup K σ)) :
    OuterIdxAt p (.twistedE6 q) (twistedE6RootGroup K σ) := by
  refine outerIdxAt_of_idxCoreAt hp ?_
  intro α hαp hαout
  haveI : Fact p.Prime := ⟨hp⟩
  have hαinner : α ∉ inner (twistedE6RootGroup K σ) :=
    fun hα => hαout (inner_le_innAutDerived _ hα)
  have hα1 : α ≠ 1 := fun h1 => hαout (by rw [h1]; exact one_mem _)
  have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
  have hK2 : Nat.card K = (q.p ^ q.exponent) ^ 2 := by
    rw [hK, TauCeti.PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := by
    intro c; rw [← TauCeti.PrimePower.card_def]; exact hσ c
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K hK2
      σ hσ'
  have hC : commutator (twistedE6RootGroup K σ) = ⊤ :=
    commutator_twistedE6RootGroup_eq_top q.prime_p q.exponent_pos hK2 σ hσ'
  have hαo : α ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    intro hα
    exact hαout (commutator_le_innAutDerived _
      (CFSG.HardMathSupport.Dickson.Sec6.I923.twistedE6Inndiag_le_commutator σ hK2 hσ' hC hα))
  have hK2' : Nat.card K = q.p ^ (2 * q.exponent) := by
    rw [hK2, ← pow_mul, mul_comm]
  obtain ⟨hηo, hpdivf, ψ, hψ⟩ :=
    exists_conj_fieldActor_of_not_mem_twistedE6Inndiag q.prime_p q.exponent_pos K hK2' σ hσ' Θ hΘ
      hp hp2 hαp hαo
  let δ : MulAut (twistedE6RootGroup K σ) := fieldActor (t := TwistTag.E6) σ (Θ α)
  let T : Subgroup (twistedE6RootGroup K σ) := twFJ σ (Θ α)
  have hcommT : ⁅fixedSubgroup δ, fixedSubgroup δ⁆ = T := by
    change ⁅fixedSubgroup (fieldActor (t := TwistTag.E6) σ (Θ α)),
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ (Θ α))⁆ = twFJ σ (Θ α)
    exact commutator_fixedSubgroup_eq_twFJ (ℓ := q.p) (f := q.exponent) q.prime_p q.exponent_pos
      hK2 σ hσ' hp hp2 hηo
  have hTle : T ≤ fixSubgroup δ := by
    change T ≤ fixedSubgroup (fieldActor (t := TwistTag.E6) σ (Θ α))
    exact twFJ_le_twR σ (Θ α)
  have hTn : ∀ f ∈ fixSubgroup δ, ∀ t ∈ T, f * t * f⁻¹ ∈ T := by
    change ∀ f ∈ fixedSubgroup (fieldActor (t := TwistTag.E6) σ (Θ α)), ∀ t ∈ T,
      f * t * f⁻¹ ∈ T
    have hnorm : (T.subgroupOf (fixedSubgroup δ)).Normal := by
      rw [← hcommT]
      infer_instance
    intro f hf t ht
    have htH : t ∈ fixedSubgroup δ := by
      have hle := Subgroup.commutator_le_sup (H₁ := fixedSubgroup δ) (H₂ := fixedSubgroup δ)
        (by rwa [← hcommT] at ht)
      simpa using hle
    have ht' : (⟨t, htH⟩ : fixedSubgroup δ) ∈ T.subgroupOf (fixedSubgroup δ) := ht
    exact hnorm.conj_mem ⟨t, htH⟩ ht' ⟨f, hf⟩
  have hp2' : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  obtain ⟨q₀, hq₀p, hqq, hF⟩ :=
    exists_primePower_fixSubfield_twisted (m := 2) (by norm_num) hK (Θ α) hp hp2' hηo
  have hd0 : 1 ≤ q.exponent / p :=
    Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpdivf) hp.pos
  have hqℓ : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hQp : (q.p ^ (q.exponent / p)) ^ p = q.p ^ q.exponent := by
    rw [← pow_mul, Nat.div_mul_cancel hpdivf]
  have hq₀card : q₀.card = q.p ^ (q.exponent / p) := by
    apply Nat.pow_left_injective hp.pos.ne'
    calc q₀.card ^ p = q.card := hqq.symm
      _ = q.p ^ q.exponent := hqℓ
      _ = (q.p ^ (q.exponent / p)) ^ p := hQp.symm
  have hσ₀ : ∀ x : ↥(fixSubfield (Θ α)),
      fixSubfieldRestrict σ (Θ α) x = x ^ q₀.card :=
    fixSubfieldRestrict_eq_pow_twE6 hqq (hp.odd_of_ne_two hp2) σ hσ (Θ α) hF
  have hσ₀' : ∀ x : ↥(fixSubfield (Θ α)),
      (fixSubfieldRestrict σ (Θ α)).toRingHom x = x ^ (q.p ^ (q.exponent / p)) := by
    intro x
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, ← hq₀card]
    exact hσ₀ x
  have hk2 : Nat.card (fixSubfield (Θ α)) = (q.p ^ (q.exponent / p)) ^ 2 := by
    rw [hF, hq₀card]
  let e₂ : Nonempty (CFSG.LieType.SeitzGeneration.Cat
      ⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩ ≃*
      twistedE6RootGroup (fixSubfield (Θ α)) (fixSubfieldRestrict σ (Θ α))) :=
    catEquiv_graphFixedRootGroup_of_data TwistTag.E6
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q₀
      (TauCeti.LieTypeIndex.valid_twistedE6 q₀) (fixSubfield (Θ α)) hF
      (fixSubfieldRestrict σ (Θ α)) hσ₀
  obtain ⟨eCat0⟩ := e₂
  let eT0 : T ≃* twistedE6RootGroup (fixSubfield (Θ α)) (fixSubfieldRestrict σ (Θ α)) :=
    (Subgroup.subgroupOfEquivOfLe (subfieldRootGroupImage_le_twistedE6 σ (Θ α))).trans
      ((Subgroup.equivMapOfInjective
        (graphFixedRootGroup TwistTag.E6 (fixSubfield (Θ α))
          (fixSubfieldRestrict σ (Θ α)).toRingHom)
        (baseChangeGL (fixSubfield (Θ α)).subtype)
        (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield (Θ α)).subtype)).symm)
  have hcardT : Nat.card T = CFSG.Open.ordTwistedE6 (q.p ^ (q.exponent / p)) := by
    rw [Nat.card_congr eT0.toEquiv]
    exact CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 q.prime_p hd0 hk2
      (fixSubfieldRestrict σ (Θ α)).toRingHom hσ₀'
  have h27T : 27 ∣ Nat.card T := by
    rw [hcardT]
    exact CFSG.HardMathSupport.Lang.E27.twentySeven_dvd_ordTwistedE6 (q.p ^ (q.exponent / p))
      (Nat.one_le_pow _ _ q.prime_p.pos)
  have hTcat : Nonempty (T ≃* (TauCeti.CFSGIndex.lie
      ⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩).Group) :=
    ⟨eT0.trans eCat0.symm⟩
  obtain ⟨eTcat⟩ := hTcat
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie
      ⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩).Group :=
    isSimpleGroup_cat_twistedE6' _
  haveI : IsSimpleGroup T := eTcat.isSimpleGroup
  have hncT : ∃ u v : T, u * v ≠ v * u := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative T := ⟨⟨fun u v => h u v⟩⟩
    have hprime : Nat.Prime (Nat.card T) :=
      (Group.is_simple_iff_prime_card (α := T)).1 inferInstance
    have h3 : 3 ∣ Nat.card T := dvd_trans (by norm_num : 3 ∣ 27) h27T
    have hcard3 : Nat.card T = 3 :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three hprime).1 h3 |>.symm
    have h27 : 27 ∣ 3 := by rwa [hcard3] at h27T
    norm_num at h27
  have hTq : CFSG.IsQuasisimple T :=
    CFSG.ClassicalInvolution.Asc77.T3Core.isQuasisimple_of_simple_nonabelian hncT
  have hZT : Subgroup.center T = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
    · exact h
    · exfalso
      obtain ⟨u, v, huv⟩ := hncT
      exact huv (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top v) u)
  have hTp : p ∣ Nat.card T := by
    rw [hcardT]
    by_cases h3 : p = 3
    · subst h3
      exact dvd_trans (by norm_num : 3 ∣ 27)
        (CFSG.HardMathSupport.Lang.E27.twentySeven_dvd_ordTwistedE6 _
          (Nat.one_le_pow _ _ q.prime_p.pos))
    · have hp3 : 3 < p := by
        have := hp.two_le
        omega
      have hcardM : Nat.card (twistedE6RootGroup K σ) =
          CFSG.Open.ordTwistedE6 (q.p ^ q.exponent) :=
        CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 q.prime_p q.exponent_pos hK2
          σ.toRingHom hσ'
      have hpord : p ∣ CFSG.Open.ordTwistedE6 (q.p ^ q.exponent) := by
        rw [← hcardM]; exact hpdvd
      have hnum_big : p ∣ CFSG.SeitzReduction.E6Pilot.numTwistedE6 (q.p ^ q.exponent) := by
        rw [← CFSG.SeitzReduction.E6Pilot.ordTwistedE6_mul_gcd (q.p ^ q.exponent)]
        exact dvd_mul_of_dvd_left hpord _
      have hnum_sub : p ∣ CFSG.SeitzReduction.E6Pilot.numTwistedE6
          ((q.p ^ (q.exponent / p)) ^ p) := by
        rw [hQp]; exact hnum_big
      exact dvd_ordTwistedE6_of_dvd_numTwistedE6 hp hp3
        (Nat.pow_pos q.prime_p.pos) hnum_sub
  have hcoreδ : IdxCoreAt p (.twistedE6 q) δ := by
    refine ⟨T, hTle, hTn, hTq, hTp, ?_⟩
    refine ⟨.lie ⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩, ⟨?_⟩, ?_⟩
    · exact (QuotientGroup.quotientMulEquivOfEq hZT).trans
        (QuotientGroup.quotientBot.trans eTcat)
    · refine Or.inl ⟨trivial, ?_⟩
      show q₀.card ^ p = q.card
      rw [hqq]
  exact idxCoreAt_of_conj hcoreδ ψ hψ

private theorem outerIdxAt_twistedE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (hpdvd : p ∣ Nat.card (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩)) :
    OuterIdxAt p (.twistedE6 q) (CFSG.LieType.SeitzGeneration.Cat ⟨.twistedE6 q, hv⟩) := by
  obtain ⟨K, _, σ, hK, hσ, ⟨e0⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hK' : Nat.card K = q.card ^ 2 := by
    rw [hK, TauCeti.PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ q.card := by
    intro c; rw [TauCeti.PrimePower.card_def]; exact hσ c
  have hpdvd' : p ∣ Nat.card (twistedE6RootGroup K σ) := by
    rw [← Nat.card_congr e0.toEquiv]
    exact hpdvd
  exact outerIdxAt_of_mulEquiv hp e0.symm
    (outerIdxAt_twistedE6Model hp hp2 hK' σ hσ' hpdvd')

theorem lieOuterIdx_excTwisted : LieOuterIdx isExcTwistedIdx := by
  rintro ⟨d, hd⟩ p hp hp2 hpc hP hpdvd hnExc
  cases d with
  | twistedE6 q => exact outerIdxAt_twistedE6 hp hp2 hd hpdvd
  | suzuki m => exact outerIdxAt_suzuki hp hp2 hd hnExc hpdvd
  | reeG2 m =>
    have hp3 : p ≠ 3 := fun h =>
      hpc (by rw [h, TauCeti.LieTypeIndex.characteristic_reeG2])
    exact outerIdxAt_reeG2 hp hp2 hp3 hd hpdvd
  | reeF4 m => exact outerIdxAt_reeF4 hp hp2 hd hpdvd
  | tits => exact outerIdxAt_tits hp hp2
  | A n q => exact absurd hP (by simp [isExcTwistedIdx])
  | twistedA n q => exact absurd hP (by simp [isExcTwistedIdx])
  | B n q => exact absurd hP (by simp [isExcTwistedIdx])
  | C n q => exact absurd hP (by simp [isExcTwistedIdx])
  | D n q => exact absurd hP (by simp [isExcTwistedIdx])
  | twistedD n q => exact absurd hP (by simp [isExcTwistedIdx])
  | E6 q => exact absurd hP (by simp [isExcTwistedIdx])
  | E7 q => exact absurd hP (by simp [isExcTwistedIdx])
  | E8 q => exact absurd hP (by simp [isExcTwistedIdx])
  | F4 q => exact absurd hP (by simp [isExcTwistedIdx])
  | G2 q => exact absurd hP (by simp [isExcTwistedIdx])
  | trialityD4 q => exact absurd hP (by simp [isExcTwistedIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
