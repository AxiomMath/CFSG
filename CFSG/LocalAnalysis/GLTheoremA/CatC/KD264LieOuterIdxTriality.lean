module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TrialityFixed
public import CFSG.Adapters.CatalogueFieldBridges.Exceptional
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerFamD4
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdx

public section

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.E6Descent
open CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
open CFSG.Adapters.CatalogueFieldBridges

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem idxCoreAt_fieldActor_canonicalD4 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (q.p ^ q.exponent) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q.p ^ q.exponent)
    (δ : K ≃+* K) (hδord : orderOf δ = p)
    (hδ : ∀ c, δ c = c ^ q.p ^ (3 * (q.exponent / p))) (hpf : p ∣ q.exponent)
    (hdq : p ∣ (q.p ^ q.exponent) ^ 6 - 1 ∨
      p ∣ (q.p ^ q.exponent) ^ 4 - (q.p ^ q.exponent) ^ 2 + 1) :
    IdxCoreAt p (.trialityD4 q) (fieldActor (t := TwistTag.D4) σ δ) := by
  classical
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hd0 : 0 < q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
  let q₀ : TauCeti.PrimePower := ⟨q.p, q.exponent / p, q.prime_p, hd0⟩
  have hq₀card : q₀.card = q.p ^ (q.exponent / p) := TauCeti.PrimePower.card_def q₀
  have hv₀ : (TauCeti.LieTypeIndex.trialityD4 q₀).Valid :=
    TauCeti.LieTypeIndex.valid_trialityD4 q₀
  have hdq' : q.card = q₀.card ^ p := by
    rw [TauCeti.PrimePower.card_def q, hq₀card, ← pow_mul, Nat.div_mul_cancel hpf]
  set d := q.exponent / p with hd
  have hdp : d * p = q.exponent := Nat.div_mul_cancel hpf
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = q.p ^ (3 * d * p) := by
    rw [hK, ← hdp, ← pow_mul]
    congr 1
    ring
  have hσ' : ∀ c, σ c = c ^ q.p ^ (d * p) := fun c => by rw [hσ, ← hdp]
  obtain ⟨-, -, hk0, -, -, -, hfixJ, hsimpJ, hncJ, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel
      q.prime_p (by omega) hp.two_le hm3 K hK' σ hσ' δ hδ
  have hFcan : Nat.card (fixSubfield δ) = q₀.card ^ 3 := by
    rw [hk0, hq₀card, ← pow_mul, mul_comm]
  let e3 : ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) ≃*
      ↥(trialityFieldImage σ δ) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  haveI : IsSimpleGroup ↥(trialityFieldImage σ δ) := hsimpJ
  haveI : IsSimpleGroup ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) := e3.isSimpleGroup
  have hncCan : ∃ a b : ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)), a * b ≠ b * a := by
    have hncJ' : ∃ a b : ↥(trialityFieldImage σ δ), a * b ≠ b * a := by
      simpa only [not_forall, ne_eq] using hncJ
    obtain ⟨a, b, hab⟩ := hncJ'
    refine ⟨e3.symm a, e3.symm b, fun h => hab ?_⟩
    have h' := congrArg e3 h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    exact h'
  have hTq : CFSG.IsQuasisimple ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncCan).1
  have hZT : Subgroup.center ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncCan).2
  have hTp : p ∣ Nat.card ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ)) := by
    have hnc : ¬ Nat.Coprime p (Nat.card (trialityFieldImage σ δ)) :=
      not_coprime_card_trialityFieldImage' q.prime_p q.exponent_pos K hK σ hσ hp (by omega) hpf hdq
        δ hδ
    rw [Nat.Prime.dvd_iff_not_coprime hp, Nat.card_congr e3.toEquiv]
    exact hnc
  have hKq : Nat.card K = q.card ^ 3 := by rw [hK, TauCeti.PrimePower.card_def]
  have hσq : ∀ c, σ c = c ^ q.card := fun c => by rw [hσ, TauCeti.PrimePower.card_def]
  obtain ⟨eCat⟩ := trialityD4_fixedSubgroup_equiv_cat hdq' hp hp5 hKq σ hσq hδord hFcan hv₀
  refine ⟨fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ), le_rfl, ?_, hTq, hTp,
    ⟨.lie ⟨.trialityD4 q₀, hv₀⟩, ?_, ?_⟩⟩
  · intro f hf t ht
    change fieldActor (t := TwistTag.D4) σ δ (f * t * f⁻¹) = f * t * f⁻¹
    have hf' : fieldActor (t := TwistTag.D4) σ δ f = f := hf
    have ht' : fieldActor (t := TwistTag.D4) σ δ t = t := ht
    rw [map_mul, map_mul, map_inv, hf', ht']
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hZT).trans
      (QuotientGroup.quotientBot.trans eCat)⟩
  · refine Or.inl ⟨trivial, ?_⟩
    show q₀.card ^ p = q.card
    rw [hdq']

theorem idxCoreAt_fieldActor_trialityD4 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = q.card ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ q.card)
    (Θ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K))
    (hΘ : ∀ α g δ, α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ → Θ α = δ)
    (x : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range)
    (hdq : p ∣ (q.p ^ q.exponent) ^ 6 - 1 ∨
      p ∣ (q.p ^ q.exponent) ^ 4 - (q.p ^ q.exponent) ^ 2 + 1) :
    IdxCoreAt p (.trialityD4 q) x := by
  classical
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hKpq : Nat.card K = (q.p ^ q.exponent) ^ 3 := by
    rw [hK, TauCeti.PrimePower.card_def]
  have hσpf : ∀ c, σ c = c ^ q.p ^ q.exponent := fun c => by
    rw [hσ, TauCeti.PrimePower.card_def]
  obtain ⟨hηp', hpf, ⟨h₀, hconj⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial q.prime_p q.exponent_pos
      K hKpq σ hσpf Θ hΘ hp (by omega : 3 < p) ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxo
      (by rw [Subgroup.orderOf_mk]; exact hxp)
  have hd0 : 0 < q.exponent / p := Nat.div_pos (Nat.le_of_dvd q.exponent_pos hpf) hp.pos
  set d := q.exponent / p with hd
  have hdp : d * p = q.exponent := Nat.div_mul_cancel hpf
  have hK3 : Nat.card K = q.p ^ (3 * q.exponent) := by
    rw [hK, TauCeti.PrimePower.card_def, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hφord, hφgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality q.prime_p
      (by have := q.exponent_pos; omega) hK3
  set δc := φ ^ (3 * d) with hδcdef
  have hδc : ∀ c, δc c = c ^ q.p ^ (3 * d) := fun c => ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [hδcdef, orderOf_pow_of_dvd (by have := hd0; omega : 3 * d ≠ 0)
      (by rw [hφord]; exact ⟨p, by rw [← hdp, mul_assoc]⟩), hφord]
    rw [← hdp, ← mul_assoc, Nat.mul_div_cancel_left p (by have := hd0; omega)]
  haveI : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; have := q.exponent_pos; omega)
  have hzp : Subgroup.zpowers (Θ x) = Subgroup.zpowers δc :=
    CFSG.RankThree.PartOne.CTP.zpowers_ringEquiv_eq_of_orderOf q.prime_p
      (by have := q.exponent_pos; omega) hK3 hηp' hδcord
  have hfix_eq : fixedSubgroup (fieldActor (t := TwistTag.D4) σ (Θ x)) =
      fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc) :=
    CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
  have hfix_eq' : fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ x)) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := hfix_eq
  have hcoreCan := idxCoreAt_fieldActor_canonicalD4 hv hp hp5 hKpq σ hσpf δc hδcord
    (fun c => by rw [hδc, hd]) hpf hdq
  have hcoreEta : IdxCoreAt p (.trialityD4 q) (fieldActor (t := TwistTag.D4) σ (Θ x)) := by
    obtain ⟨T, hTF, hN, hTq, hTp, i, he, hr⟩ := hcoreCan
    refine ⟨T, ?_, ?_, hTq, hTp, i, he, hr⟩
    · rw [hfix_eq']; exact hTF
    · intro f hf t ht
      rw [hfix_eq'] at hf
      exact hN f hf t ht
  exact idxCoreAt_of_conj hcoreEta (MulAut.conj h₀) hconj

theorem lieOuterIdx_triality : LieOuterIdx isTrialityIdx := by
  rintro ⟨d, hv⟩ p hp hp2 hpc hP hpdvd hnexc
  cases d with
  | trialityD4 q =>
    have hp3 : p ≠ 3 := by
      intro h3
      exact hnexc (Or.inl ⟨h3, Or.inr ⟨q, rfl⟩⟩)
    have hp5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · norm_num at hp
        · norm_num at hp
        · exact absurd rfl hp2
        · exact absurd rfl hp3
        · norm_num at hp
      · exact h
    have hpq : q.p ≠ p := by
      intro h
      exact hpc (by rw [TauCeti.LieTypeIndex.characteristic_trialityD4]; exact h.symm)
    obtain ⟨K, hfield, hfinite, σ, hK, hσ, -, ⟨eK⟩⟩ := exists_catEquiv_trialityD4 q hv
    letI := hfield
    letI := hfinite
    have hpdvdCat : p ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := hpdvd
    haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
    haveI : Finite (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group :=
      Finite.of_equiv ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) eK.symm.toEquiv
    obtain ⟨m, hm, hdvdphi⟩ :=
      ((exact_E_type_and_triality_cross_prime_factor_exhaustion (ℓ := q.p) (f := q.exponent)
        hp (by omega : 3 < p) hpq (chevalleyModel_cat_trialityD4 hv)).1 hpdvdCat).2.2.2.2 rfl
    have hdq : p ∣ (q.p ^ q.exponent) ^ 6 - 1 ∨
        p ∣ (q.p ^ q.exponent) ^ 4 - (q.p ^ q.exponent) ^ 2 + 1 := by
      by_cases h6 : p ∣ (q.p ^ q.exponent) ^ 6 - 1
      · exact Or.inl h6
      · exact Or.inr (dvd_phi12_of_exhaustion (Nat.one_le_pow _ _ q.prime_p.pos) h6 hm hdvdphi)
    obtain ⟨Θ, hΘ, hΘker⟩ := exists_hom_trialityD4 q.prime_p q.exponent_pos K hK σ hσ
    have hcore : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        x ^ p = 1 → x ∉ innAutDerived ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
        IdxCoreAt p (.trialityD4 q) x := by
      intro x hxp hxo
      have hx1 : Θ x ≠ 1 := fun h1 => hxo (by
        have h2 : x ∈ Θ.ker := h1
        rw [hΘker] at h2
        exact inner_le_innAutDerived _ h2)
      haveI : Fact p.Prime := ⟨hp⟩
      have hxord : orderOf x = p :=
        orderOf_eq_prime hxp (by rintro rfl; exact hxo (Subgroup.one_mem _))
      have hKq : Nat.card K = q.card ^ 3 := by rw [hK, TauCeti.PrimePower.card_def]
      have hσq : ∀ c, σ c = c ^ q.card := fun c => by
        rw [hσ, TauCeti.PrimePower.card_def]
      have hxr : x ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
          MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
        fun h => hxo (inner_le_innAutDerived _ h)
      exact idxCoreAt_fieldActor_trialityD4 hv hp hp5 hKq σ hσq Θ hΘ x hxord hxr hdq
    exact outerIdxAt_of_mulEquiv hp eK.symm (outerIdxAt_of_idxCoreAt hp hcore)
  | A n q => exact absurd hP (by simp [isTrialityIdx])
  | twistedA n q => exact absurd hP (by simp [isTrialityIdx])
  | B n q => exact absurd hP (by simp [isTrialityIdx])
  | C n q => exact absurd hP (by simp [isTrialityIdx])
  | D n q => exact absurd hP (by simp [isTrialityIdx])
  | twistedD n q => exact absurd hP (by simp [isTrialityIdx])
  | E6 q => exact absurd hP (by simp [isTrialityIdx])
  | E7 q => exact absurd hP (by simp [isTrialityIdx])
  | E8 q => exact absurd hP (by simp [isTrialityIdx])
  | F4 q => exact absurd hP (by simp [isTrialityIdx])
  | G2 q => exact absurd hP (by simp [isTrialityIdx])
  | twistedE6 q => exact absurd hP (by simp [isTrialityIdx])
  | suzuki k => exact absurd hP (by simp [isTrialityIdx])
  | reeG2 k => exact absurd hP (by simp [isTrialityIdx])
  | reeF4 k => exact absurd hP (by simp [isTrialityIdx])
  | tits => exact absurd hP (by simp [isTrialityIdx])

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
