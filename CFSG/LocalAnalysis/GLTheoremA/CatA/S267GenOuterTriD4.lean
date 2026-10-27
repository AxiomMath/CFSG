module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenOuterTriA2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

section Field

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley


theorem compsNormal_triD4_field {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφp : φ ^ p = 1)
    (hφout : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    CompsNormal ↥(fixSubgroup φ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hφ1 : φ ≠ 1 := fun h => hφout (h ▸ one_mem _)
  have hφord : orderOf φ = p := orderOf_eq_prime hφp hφ1
  obtain ⟨-, -, Θ, hΘ, -⟩ := triality_normal_form_data hℓ hf K hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ Θ hΘ hp
      (by omega) ⊤ le_top ⟨φ, Subgroup.mem_top _⟩ hφout
      (by rw [Subgroup.orderOf_mk]; exact hφord)
  have hh₀' : MulAut.conj h₀ * φ * (MulAut.conj h₀)⁻¹ =
      fieldActor (t := TwistTag.D4) σ (Θ φ) := hh₀
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'
      omega
    · exact h
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨φ', hφ', hφord', -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ' ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ' _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega)
      (by rw [hφord', hff']; exact ⟨p, by ring⟩), hφord', hff',
      show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ φ) = Subgroup.zpowers δc :=
    CFSG.RankThree.PartOne.CTP.zpowers_ringEquiv_eq_of_orderOf hℓ (by omega : 1 ≤ 3 * f) hK3
      hηord hδcord
  have hfix_eq : fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ φ)) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, -, -, -, -, hfixJ, hsimpJ, -, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd hp.two_le hm3 K hK' σ
      hσ' δc hδc
  haveI := hsimpJ
  set δ₀ := fieldActor (t := TwistTag.D4) σ δc with hδ₀
  have e3 : ↥(fixSubgroup δ₀) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hsimE : IsSimpleGroup ↥(fixSubgroup δ₀) := e3.isSimpleGroup
  have hδ : CompsNormal ↥(fixSubgroup δ₀) := compsNormal_of_isSimpleGroup
  have h' : CompsNormal ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ φ))) :=
    compsNormal_fixSubgroup_of_eq hfix_eq.symm hδ
  refine compsNormal_fixSubgroup_of_conj (MulAut.conj h₀) φ ?_
  rw [hh₀']
  exact h'

end Field

section Graph

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (nonempty_fixSubgroup_fieldActor_equiv_G2
  ExcCopy.isPerfect_adjointGroup ExcCopy.isSimpleGroup_adjointGroup_of_perfect)

private theorem compsNormal_of_conj_eq {Y : Type} [Group Y] (y : Y) {φ ψ : MulAut Y}
    (h : MulAut.conj y * φ * (MulAut.conj y)⁻¹ = ψ) (hψ : CompsNormal ↥(fixSubgroup ψ)) :
    CompsNormal ↥(fixSubgroup φ) :=
  compsNormal_fixSubgroup_of_conj (MulAut.conj y) φ (h ▸ hψ)


theorem compsNormal_fieldActor_self {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    CompsNormal ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := by
  classical
  obtain ⟨e⟩ := nonempty_fixSubgroup_fieldActor_equiv_G2 (by omega) hf (Or.inr hℓ5) hK σ hσ
  haveI : Finite (fixSubfield σ) := Subtype.finite
  have hq2 : 2 ≤ ℓ ^ f := le_trans (by omega) (Nat.le_self_pow (by omega) ℓ)
  have hk : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixedField_of_cube σ.toRingHom hq2 hK hσ
  have hk3 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hk]
    exact le_trans (by omega) (Nat.le_self_pow (by omega) ℓ)
  obtain ⟨hs, -⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect .G2 (fixSubfield σ)
    (ExcCopy.isPerfect_adjointGroup .G2 (fixSubfield σ) fun _ => hk3)
  haveI := hs
  exact (compsNormal_of_isSimpleGroup).of_mulEquiv e

variable {p f : ℕ}

private theorem compsNormal_cocycle_q1 (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    CompsNormal ↥(fixSubgroup (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ)) := by
  have hRot := rotLang_holds
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hG2 : CompsNormal ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) :=
    compsNormal_fieldActor_self hp5 hf hK σ hσ
  obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
  refine compsNormal_of_conj_eq y hyn ?_
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨y', s, -, -, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
    refine compsNormal_of_conj_eq y' hconj ?_
    by_cases hd1 : d = 1
    · have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      rw [hs1, map_one, one_mul]
      exact hG2
    · exact compsNormal_a2Plus hp hp2 hf hq hK hσ hd hd3 hd1 hsd
  · obtain ⟨y₀, s, d, hconj, hd, hd3, hd1, hsd⟩ :=
      ellQ1_conj_toral hRot hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
    refine compsNormal_of_conj_eq y₀ hconj ?_
    exact compsNormal_a2Plus hp hp2 hf hq hK hσ hd hd3 hd1 hsd

theorem compsNormal_outer_three_odd_one {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    (hq : (ℓ ^ f) % 3 = 1) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    CompsNormal ↥(fixSubgroup φ) := by
  have hp : ℓ.Prime := Fact.out
  have hp2 : ℓ ≠ 2 := by omega
  have hp3 : ℓ ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨g, hg, hφ' | hφ'⟩ := d4_outer_three_normal_form hp hp2 hf K₃ hK₃ Fr hFr φ hφord hφ
  · rw [hφ']
    exact compsNormal_cocycle_q1 hp hp2 hp3 hf hq hK₃ Fr hFr g hg
  · have h := compsNormal_cocycle_q1 hp hp2 hp3 hf hq hK₃ Fr hFr g hg
    rw [← hφ'] at h
    exact compsNormal_fixSubgroup_of_eq (fixSubgroup_inv_eq φ) h

theorem compsNormal_outer_three_odd_two {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f)
    (hq : (ℓ ^ f) % 3 = 2) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    CompsNormal ↥(fixSubgroup φ) := by
  have hp : ℓ.Prime := Fact.out
  have hp2 : ℓ ≠ 2 := by omega
  have hp3 : ℓ ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot Fr.surjective
  have hψ3 := d4_fieldActor_pow_three K₃ hK₃ Fr hFr
  have hG2 : CompsNormal ↥(fixSubgroup (fieldActor (t := TwistTag.D4) Fr Fr)) :=
    compsNormal_fieldActor_self hℓ5 hf hK₃ Fr hFr
  have hTor : ∀ s, D4MinusToral ℓ f hp K₃ Fr s →
      CompsNormal ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) Fr Fr)) :=
    fun s hs => compsNormal_a2Minus hp hp2 hp3 hf hq hK₃ hFr hs
  rcases d4Minus_outer_three_nf hp hp2 hp3 hf hq K₃ hK₃ Fr hFr φ hφord hφ with
    ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ | ⟨y, n, hn, hyn⟩
  · rcases hy with hy | hy
    · exact compsNormal_of_conj_eq y hy hG2
    · exact compsNormal_of_conj_eq y hy (compsNormal_fixSubgroup_inv hG2)
  · rcases hys with hys | hys
    · exact compsNormal_of_conj_eq y hys (hTor s hs)
    · exact compsNormal_of_conj_eq y hys (compsNormal_fixSubgroup_inv (hTor s hs))
  · have hc := pow_three_of_conj_eq y hφ3 hyn
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hc
    obtain ⟨y₀, s, hsT, hconj⟩ :=
      minusEll_conj_toral rotLang_holds hp hp2 hp3 hf hq hK₃ Fr hFr n hn hN
    have hPL := compsNormal_of_conj_eq y₀ hconj (hTor s hsT)
    rcases hyn with hyn | hyn
    · exact compsNormal_of_conj_eq y hyn hPL
    · exact compsNormal_of_conj_eq y hyn (compsNormal_fixSubgroup_inv hPL)

end Graph

section Cat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner_le_innAutDerived
  mem_innAutDerived_congr)


theorem compsNormal_triD4_cat (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq2 : q.p ≠ 2) {S : Type} [Group S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q.p) (β : MulAut S) (hβ : β ^ p = 1) (hout : β ∉ innAutDerived S) :
    CompsNormal ↥(fixSubgroup β) := by
  classical
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  let e' : S ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := e.trans eK
  refine compsNormal_fixSubgroup_of_congr e' ?_
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : MulAut.congr e' β ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom) →* MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun h =>
    hout ((mem_innAutDerived_congr e').1 (inner_le_innAutDerived _ h))
  have hℓ := q.prime_p
  by_cases hp3 : p = 3
  · subst hp3
    haveI : Fact q.p.Prime := ⟨hℓ⟩
    have hℓ5 : 5 ≤ q.p := by
      have := hℓ.two_le
      have h4 : q.p ≠ 4 := fun h => by rw [h] at hℓ; exact absurd hℓ (by norm_num)
      omega
    have hq3 : ¬ 3 ∣ q.p ^ q.exponent := fun h =>
      absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
        (Nat.prime_three.dvd_of_dvd_pow h)) hpq
    rcases (show (q.p ^ q.exponent) % 3 = 1 ∨ (q.p ^ q.exponent) % 3 = 2 by omega) with h1 | h1
    · exact compsNormal_outer_three_odd_one hℓ5 q.exponent_pos h1 hK σ hσ _ hβ' hout'
    · exact compsNormal_outer_three_odd_two hℓ5 q.exponent_pos h1 hK σ hσ _ hβ' hout'
  · have hp5 : 5 ≤ p := by
      have := hp.two_le
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
      omega
    exact compsNormal_triD4_field hℓ q.exponent_pos hK σ hσ hp hp5 _ hβ' hout'

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
