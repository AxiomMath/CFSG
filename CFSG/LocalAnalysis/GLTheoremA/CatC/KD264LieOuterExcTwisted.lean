module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
public import CFSG.LocalAnalysis.ComponentClassification.LieOrderNumeratorMod
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSuzuki
public import CFSG.LieType.Chevalley.TwistedE6RootGroupPerfect
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTwField
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeG2Core
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Core
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core
public import CFSG.LieType.SeitzGeneration.ExcParabolicTits
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Reduction

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.CatLeaf
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.LieType.Ree
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)


namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


private theorem outerPLayerAt_tits {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {hv : TauCeti.LieTypeIndex.tits.Valid} {S : Type} [Group S] [Finite S]
    (e : S ≃* CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩) :
    OuterPLayerAt p S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmodel : CFSG.Blueprint.ReeTitsModel
      (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩) .Tits 2 1 :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_tits
      (S := CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩)
      ⟨hv, ⟨MulEquiv.refl _⟩⟩
  haveI : Finite (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩) :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.LieType.SeitzGeneration.card_cat_tits hv]; norm_num)
  obtain ⟨h2, -⟩ :=
    CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier _ 2 1 hmodel
  have hout : OuterPLayerAt p
      (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩) := by
    intro b hbp hbout
    exfalso
    have hpow : (QuotientGroup.mk b :
        Outer (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩)) ^ p = 1 := by
      rw [← QuotientGroup.mk_pow, hbp, QuotientGroup.mk_one]
    have hdiv1 : orderOf (QuotientGroup.mk b : Outer _) ∣ p := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hdiv2 : orderOf (QuotientGroup.mk b : Outer _) ∣ 2 ^ n := by
      rw [← hn]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime p (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.2 (hp.odd_of_ne_two hp2))
    have hone : orderOf (QuotientGroup.mk b : Outer _) = 1 :=
      Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hdiv1 hdiv2)
    have hbin : b ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.tits, hv⟩) := by
      rw [← QuotientGroup.eq_one_iff, orderOf_eq_one_iff.1 hone]
    exact hbout (inner_le_innAutDerived _ hbin)
  exact outerPLayerAt_congr hp e.symm hout


private theorem outerPLayerAt_suzuki {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m : ℕ} (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (hnExc : ¬ outerPLayerExc p (.suzuki m)) {S : Type} [Group S] [Finite S]
    (e : S ≃* CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.suzuki m, hv⟩)
    (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e0⟩⟩ :=
    CFSG.LieType.SeitzGeneration.suzukiModel_cat hv
  have ham : m = a := by omega
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have eS : S ≃* CFSG.Blueprint.suzukiGroup a F := e.trans e0
  have hpdvdM : p ∣ Nat.card (CFSG.Blueprint.suzukiGroup a F) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  refine outerPLayerAt_of_mulEquiv_of_glaPLayer hp eS ?_
  intro x hxp hxout
  haveI : Fact p.Prime := ⟨hp⟩
  have hxinner : x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Blueprint.suzukiGroup a F) := fun hx => hxout (inner_le_innAutDerived _ hx)
  have hx1 : x ≠ 1 := fun h1 => hxout (by rw [h1]; exact one_mem _)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  obtain ⟨σ, h, b, k, _, _, _, hbp, hkc, hconj, ⟨eH⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha F hF' p hp hp2 x hxord hxinner
  set δ := szFieldAut a F σ with hδ
  have hconj' : MulAut.congr (MulAut.conj h : CFSG.Blueprint.suzukiGroup a F ≃*
      CFSG.Blueprint.suzukiGroup a F) x = δ := by
    rw [← hconj]
    ext z
    simp [MulAut.congr_apply, MulAut.mul_apply]
  have hfixmap : fixSubgroup δ = (fixSubgroup x).map (MulAut.conj h).toMonoidHom := by
    rw [← hconj']
    exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr (MulAut.conj h) x
  obtain ⟨y, hy, hyord⟩ := exists_orderOf_eq_prime_mem_fixSubgroup hp x hxp hpdvdM
  have hpfixx : p ∣ Nat.card (fixSubgroup x) := by
    have hord : p = orderOf (⟨y, hy⟩ : fixSubgroup x) := by
      rw [Subgroup.orderOf_mk, hyord]
    rw [hord]
    exact orderOf_dvd_natCard _
  have hpfixδ : p ∣ Nat.card (fixSubgroup δ) := by
    rw [hfixmap, Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact hpfixx
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
      rw [hpdvd_eq, h20] at hpfixδ
      exact hpfixδ
    have hp5 : p = 5 := by
      have h1 : p ∣ 2 ^ 2 * 5 := by simpa using hdvd20
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
          (hp.dvd_of_dvd_pow h1)) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h1
    have ha2 : a = 2 := by omega
    exact hnExc (by simpa [outerPLayerExc] using ⟨hp5, by rw [ham]; exact ha2⟩)
  have hqk : CFSG.IsQuasisimple (CFSG.Blueprint.suzukiGroup b k) :=
    CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.isQuasisimple_suzukiGroup hb1 hkc
  let eX : fixSubgroup x ≃* CFSG.Blueprint.suzukiGroup b k :=
    ((Subgroup.equivMapOfInjective (fixSubgroup x) (MulAut.conj h).toMonoidHom
        (MulAut.conj h).injective).trans
      (MulEquiv.subgroupCongr hfixmap.symm)).trans eH
  have hq : CFSG.IsQuasisimple (fixSubgroup x) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hqk
  refine glaPLayer_fixSubgroup_ne_bot_of_quasisimple hp (x := x) (T := fixSubgroup x) le_rfl ?_
    hq hpfixx
  intro f hf t ht
  exact mul_mem (mul_mem hf ht) (inv_mem hf)

private theorem outerPLayerAt_reeG2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) {S : Type} [Group S] [Finite S]
    (e : S ≃* CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.reeG2 m, hv⟩)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S)
    (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff (.reeG2 m)).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hpq : 3 ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_reeG2] at h
  have hp3 : 3 < p := by
    have := hp.two_le
    omega
  obtain ⟨X, _, _, _, hX, ⟨e0⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat_G2 hv
  have eS : S ≃* ReeTag.G2.reeGamma X m := e.trans e0
  have hpdvdM : p ∣ Nat.card (ReeTag.G2.reeGamma X m) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  refine outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS ?_
  intro x hxp hxout
  haveI : Fact p.Prime := ⟨hp⟩
  have hxinner : x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (ReeTag.G2.reeGamma X m) := fun hx => hxout (inner_le_innAutDerived _ hx)
  obtain ⟨-, δ, σ, hσp, hconj, hkcard, hfixed⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent m hm1 X hX hp hp2
      x hxp hxinner
  set φ := ReeTag.G2.reeGammaFieldAut X m σ with hφ
  have hsem : SemiconjBy δ x φ := by
    rw [SemiconjBy]
    calc δ * x = (δ * x * δ⁻¹) * δ := by group
      _ = φ * δ := by rw [hconj]
  have hφord : orderOf φ = p := by
    rw [← SemiconjBy.orderOf_eq δ hsem, orderOf_eq_prime hxp (by
      intro h1
      exact hxinner (by rw [h1]; exact one_mem _))]
  have hφpow : φ ^ p = 1 := by rw [← hφord]; exact pow_orderOf_eq_one φ
  obtain ⟨y, hy, hyord⟩ := exists_orderOf_eq_prime_mem_fixSubgroup hp φ hφpow hpdvdM
  have hdvd : p ∣ Nat.card (φ.toMonoidHom.eqLocus (MonoidHom.id _)) := by
    have hord : p = orderOf (⟨y, hy⟩ : fixSubgroup φ) := by
      rw [Subgroup.orderOf_mk, hyord]
    rw [hord]
    exact orderOf_dvd_natCard _
  have hd : (2 * m + 1) / p = 2 * (((2 * m + 1) / p - 1) / 2) + 1 := by
    have hdvd : p ∣ 2 * m + 1 := by
      rw [← hσp, ← (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
        Nat.prime_three X hX).1]
      exact orderOf_dvd_natCard σ
    have hodd : Odd ((2 * m + 1) / p) := by
      apply Nat.not_even_iff_odd.1
      intro he
      have hoddprod : Odd (p * ((2 * m + 1) / p)) := by
        rw [mul_comm, Nat.div_mul_cancel hdvd]
        exact odd_two_mul_add_one m
      obtain ⟨c, hc⟩ := he
      have hevenprod : Even (p * ((2 * m + 1) / p)) := ⟨p * c, by rw [hc]; ring⟩
      exact Nat.not_even_iff_odd.2 hoddprod hevenprod
    obtain ⟨b, hb⟩ := hodd
    omega
  have hkcard' : Nat.card (fixSubfield σ) = 3 ^ (2 * (((2 * m + 1) / p - 1) / 2) + 1) := by
    have h := hkcard
    rw [hd] at h
    exact h
  have hcore : FieldCoreAt p φ :=
    fieldCoreAt_reeGamma_G2 hm1 hX hp hp3 hφord hkcard' hfixed hdvd
  exact fieldCoreAt_of_conj hcore δ hconj

private theorem outerPLayerAt_reeF4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {m : ℕ} (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {S : Type} [Group S] [Finite S]
    (e : S ≃* CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.reeF4 m, hv⟩)
    (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  obtain ⟨X, _, _, _, hm1, hX, _, ⟨e0⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  have eS : S ≃* ReeTag.F4.reeGamma X m := e.trans e0
  have hpdvdM : p ∣ Nat.card (ReeTag.F4.reeGamma X m) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  refine outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS ?_
  intro x hxp hxout
  haveI : Fact p.Prime := ⟨hp⟩
  have hxinner : x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (ReeTag.F4.reeGamma X m) := fun hx => hxout (inner_le_innAutDerived _ hx)
  by_cases h3 : p = 3
  · subst h3
    have h3dvd : 3 ∣ (2 ^ (2 * m + 1)) ^ 4 - 1 := by
      have h4 : (2 ^ (2 * m + 1)) ^ 4 = 4 ^ (2 * (2 * m + 1)) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [h4]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 (2 * (2 * m + 1))
    exact fieldCoreAt_reeGamma hm1 hX hp hp2 h3dvd x hxp hxinner
  · have hp3 : 3 < p := by
      have := hp.two_le
      omega
    obtain ⟨hNFex, hNFuniq⟩ := reeGamma_normalForm hm1 hX
    obtain ⟨y, σ, hxσ⟩ := hNFex x
    obtain ⟨-, hone, hpow, -⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.reeGammaFieldAut_hom_facts (K := X) (a := m)
    have hσp : σ ^ p = 1 := by
      obtain ⟨z, hz⟩ : ∃ z, (MulAut.conj y * ReeTag.F4.reeGammaFieldAut X m σ) ^ p =
          MulAut.conj z * ReeTag.F4.reeGammaFieldAut X m σ ^ p :=
        ⟨_, CFSG.RankThree.PartOne.KE.conj_mul_pow_aut y (ReeTag.F4.reeGammaFieldAut X m σ) p⟩
      have h' : MulAut.conj 1 * ReeTag.F4.reeGammaFieldAut X m 1 =
          MulAut.conj z * ReeTag.F4.reeGammaFieldAut X m (σ ^ p) := by
        rw [map_one, hone, one_mul, hpow, ← hz, ← hxσ]
        exact hxp.symm
      exact (hNFuniq _ _ _ _ h').2.symm
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      apply hxinner
      rw [hxσ, hone, mul_one]
      exact ⟨y, rfl⟩
    have hσ : orderOf σ = p := orderOf_eq_prime hσp hσ1
    obtain ⟨b, _, hkcard, hfixed⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.largeRee_fixed_data_of_odd hX hp hp2 σ hσ
    set φ := ReeTag.F4.reeGammaFieldAut X m σ with hφ
    have hφpow : φ ^ p = 1 := by
      rw [hφ, ← hpow σ p, hσp, hone]
    have hφ1 : φ ≠ 1 := by
      intro h1
      apply hxinner
      rw [hxσ, h1, mul_one]
      exact ⟨y, rfl⟩
    have hφord : orderOf φ = p := orderOf_eq_prime hφpow hφ1
    obtain ⟨z, hz, hzord⟩ := exists_orderOf_eq_prime_mem_fixSubgroup hp φ hφpow hpdvdM
    have hdvd : p ∣ Nat.card (φ.toMonoidHom.eqLocus (MonoidHom.id _)) := by
      have hord : p = orderOf (⟨z, hz⟩ : fixSubgroup φ) := by
        rw [Subgroup.orderOf_mk, hzord]
      rw [hord]
      exact orderOf_dvd_natCard _
    have hcore : FieldCoreAt p φ :=
      fieldCoreAt_reeGamma_F4 hm1 hX hp hp3 hφord hkcard hfixed hdvd
    obtain ⟨g, hg⟩ :=
      CFSG.RankThree.PartOne.RF4.largeRee_fieldAut_coset_conj m hX hp σ hσ x hxp ⟨y, hxσ⟩
    refine fieldCoreAt_of_conj hcore (MulAut.conj g)⁻¹ ?_
    rw [hg]
    group
    exact hφ.symm

theorem dvd_ordTwistedE6_of_dvd_numTwistedE6 {p Q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hQ : 0 < Q) (hdvd : p ∣ CFSG.SeitzReduction.E6Pilot.numTwistedE6 (Q ^ p)) :
    p ∣ CFSG.Open.ordTwistedE6 Q := by
  have hdiv : p / p = 1 := Nat.div_self hp.pos
  have hnum : p ∣ CFSG.SeitzReduction.E6Pilot.numTwistedE6 Q := by
    have h1 : p ∣ lieOrderNumerator .twistedE6 0 (Q ^ p) := by
      simpa [lieOrderNumerator, CFSG.SeitzReduction.E6Pilot.numTwistedE6] using hdvd
    have h2 := (prime_dvd_lieOrderNumerator_pow_iff .twistedE6 0 hp (by omega) dvd_rfl).1 h1
    simpa [hdiv, lieOrderNumerator, CFSG.SeitzReduction.E6Pilot.numTwistedE6] using h2
  have hgcd : ¬ p ∣ Nat.gcd 3 (Q + 1) := by
    intro h
    have hle : p ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 3 (Q + 1)))
    omega
  have hcop : Nat.Coprime p (Nat.gcd 3 (Q + 1)) := (hp.coprime_iff_not_dvd).2 hgcd
  have hmul := CFSG.SeitzReduction.E6Pilot.ordTwistedE6_mul_gcd Q
  rw [← hmul] at hnum
  exact hcop.dvd_of_dvd_mul_right hnum

private theorem not_coprime_card_subfield_twistedE6 {ℓ f p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hpdivf : p ∣ f)
    (hpord : p ∣ CFSG.Open.ordTwistedE6 (ℓ ^ f))
    {K : Type} [Field K] [Finite K] (κ : K ≃+* K) (hκ : ∀ c, κ c = c ^ ℓ ^ (2 * (f / p)))
    (σ₀ : fixSubfield κ ≃+* fixSubfield κ)
    (hσ₀ : ∀ c, (σ₀ c : K) = (c : K) ^ ℓ ^ (f / p))
    (hkcard : Nat.card (fixSubfield κ) = ℓ ^ (2 * (f / p))) :
    ¬ Nat.Coprime p (Nat.card (CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6
      (fixSubfield κ) σ₀)) := by
  have hdp : f / p * p = f := Nat.div_mul_cancel hpdivf
  have hd1 : 1 ≤ f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpdivf) hp.pos
  have : Finite (fixSubfield κ) := Subtype.finite
  have hk2 : Nat.card (fixSubfield κ) = (ℓ ^ (f / p)) ^ 2 := by
    rw [hkcard, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c : fixSubfield κ, σ₀.toRingHom c = c ^ (ℓ ^ (f / p)) := fun c =>
    Subtype.ext (by
      change (σ₀ c : K) = ((c ^ (ℓ ^ (f / p)) : fixSubfield κ) : K)
      rw [hσ₀ c, SubmonoidClass.coe_pow])
  have hcardJ : Nat.card (CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6
      (fixSubfield κ) σ₀) = CFSG.Open.ordTwistedE6 (ℓ ^ (f / p)) := by
    have hcard : Nat.card (CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6
        (fixSubfield κ) σ₀) = Nat.card (twistedE6RootGroup (fixSubfield κ) σ₀) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    rw [hcard]
    exact CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 (K := fixSubfield κ)
      hℓ hd1 hk2 σ₀.toRingHom hσ₀'
  have hQp : (ℓ ^ (f / p)) ^ p = ℓ ^ f := by
    rw [← pow_mul, hdp]
  have hnum_big : p ∣ CFSG.SeitzReduction.E6Pilot.numTwistedE6 (ℓ ^ f) := by
    rw [← CFSG.SeitzReduction.E6Pilot.ordTwistedE6_mul_gcd (ℓ ^ f)]
    exact dvd_mul_of_dvd_left hpord _
  have hnum_sub : p ∣ CFSG.SeitzReduction.E6Pilot.numTwistedE6 ((ℓ ^ (f / p)) ^ p) := by
    rw [hQp]; exact hnum_big
  have hdvd : p ∣ CFSG.Open.ordTwistedE6 (ℓ ^ (f / p)) :=
    dvd_ordTwistedE6_of_dvd_numTwistedE6 hp hp3 (Nat.pow_pos hℓ.pos) hnum_sub
  rw [hcardJ]
  exact fun hc => ((Nat.Prime.coprime_iff_not_dvd hp).1 hc) hdvd

private theorem outerPLayerAt_twistedE6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    {S : Type} [Group S] [Finite S]
    (e : S ≃* CFSG.LieType.SeitzGeneration.Cat ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩)
    (hnot : ¬ CFSG.Yardstones.Md0ec50421ce4.IsChevSimple p S)
    (hpdvd : p ∣ Nat.card S) : OuterPLayerAt p S := by
  have hpq : q.p ≠ p := by
    have h := characteristic_ne_of_not_isChevSimple hv ⟨e⟩ hnot
    rwa [TauCeti.LieTypeIndex.characteristic_twistedE6] at h
  obtain ⟨K, _, σ, hK, hσ, ⟨e0⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  set ℓ := q.p with hℓdef
  set f := q.exponent with hfdef
  have hKq : Nat.card K = (ℓ ^ f) ^ 2 := hK
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKq]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hKf : Nat.card K = ℓ ^ (2 * f) := by
    rw [hKq, ← pow_mul, mul_comm]
  have hσ' : ∀ c, σ c = c ^ (ℓ ^ f) := hσ
  have hcardM : Nat.card (twistedE6RootGroup K σ) = CFSG.Open.ordTwistedE6 (ℓ ^ f) :=
    CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 q.prime_p q.exponent_pos hKq
      σ.toRingHom hσ'
  have eS : S ≃* twistedE6RootGroup K σ := e.trans e0
  have hpdvdM : p ∣ Nat.card (twistedE6RootGroup K σ) := by
    rw [← Nat.card_congr eS.toEquiv]
    exact hpdvd
  have hpord : p ∣ CFSG.Open.ordTwistedE6 (ℓ ^ f) := by
    rw [← hcardM]
    exact hpdvdM
  refine outerPLayerAt_of_mulEquiv_of_fieldCoreAt hp eS ?_
  intro x hxp hxout
  haveI : Fact p.Prime := ⟨hp⟩
  have hxinner : x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (twistedE6RootGroup K σ) := fun hx => hxout (inner_le_innAutDerived _ hx)
  have hx1 : x ≠ 1 := fun h1 => hxout (by rw [h1]; exact one_mem _)
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  by_cases h3 : p = 3
  · subst h3
    have hC : commutator (twistedE6RootGroup K σ) = ⊤ :=
      commutator_twistedE6RootGroup_eq_top q.prime_p q.exponent_pos hKq σ hσ'
    have hxo : x ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      intro hx
      exact hxout (commutator_le_innAutDerived _
        (CFSG.HardMathSupport.Dickson.Sec6.I923.twistedE6Inndiag_le_commutator σ hKq hσ' hC hx))
    exact fieldCoreAt_twistedE6_of_not_mem_inndiag q.prime_p hpq q.exponent_pos K hKf σ
      hσ' hxp hxo
  · have hp3 : 3 < p := by
      have := hp.two_le
      omega
    obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
      twisted_E6_all_characteristic_exact_automorphism_normal_form q.prime_p q.exponent_pos K
        hKq σ hσ'
    obtain ⟨-, hpdivf, -⟩ :=
      twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial q.prime_p
        q.exponent_pos K hKf σ hσ' Θ hΘ hp hp3 ⊤ le_top
        ⟨x, Subgroup.mem_top x⟩ hxinner (by
          rw [Subgroup.orderOf_mk]; exact hxord)
    refine fieldCoreAt_twistedE6 q.prime_p q.exponent_pos K hKf σ hσ' Θ hΘ hp hp3
      (fun κ hκ σ₀ hσ₀ hkcard =>
        not_coprime_card_subfield_twistedE6 hp hp3 q.prime_p q.exponent_pos hpdivf hpord
          (K := K) κ hκ σ₀ hσ₀ hkcard) hxord hxinner

theorem lieOuterPLayer_excTwisted : ∀ p : ℕ, p.Prime → p ≠ 2 →
    LieOuterPLayer p isExcTwistedIdx := by
  intro p hp hp2 d hd hP hnExc S hS hfin he hnot hpdvd
  obtain ⟨e⟩ := he
  cases d with
  | twistedE6 q => exact outerPLayerAt_twistedE6 hp hp2 hd e hnot hpdvd
  | suzuki m => exact outerPLayerAt_suzuki hp hp2 hd hnExc e hpdvd
  | reeG2 m => exact outerPLayerAt_reeG2 hp hp2 hd e hnot hpdvd
  | reeF4 m => exact outerPLayerAt_reeF4 hp hp2 hd e hpdvd
  | tits => exact outerPLayerAt_tits hp hp2 e
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
