module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsNotReeComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTriD4
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Chevalley


theorem s2019OuterComp_trialityD4 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    {K : Type} [Group K] [Finite K]
    (eK : K ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group)
    (β : MulAut K) (hβ : β ^ p = 1) (hout : ∀ a : K, MulAut.conj a ≠ β)
    (J : Subgroup K) (hJ : IsComponentOf J (fixSubgroup β)) :
    Subgroup.center ↥J = ⊥ ∧
      ∃ (q' : TauCeti.PrimePower) (hv' : (TauCeti.LieTypeIndex.trialityD4 q').Valid),
        q'.card ^ p = q.card ∧
          Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hv'⟩).Group) := by
  classical
  obtain ⟨K₃, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  set ℓ := q.p with hℓdef
  set f := q.exponent with hfdef
  have hℓ : ℓ.Prime := q.prime_p
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hf : 1 ≤ f := q.exponent_pos
  haveI : Fact p.Prime := ⟨hp⟩
  set C := graphFixedRootGroup TwistTag.D4 K₃ σ.toRingHom with hC
  let e' : K ≃* C := eK.trans eC
  set φ := MulAut.congr e' β with hφdef
  have hφp : φ ^ p = 1 := by rw [hφdef, ← map_pow, hβ, map_one]
  have hφout : φ ∉ (MulAut.conj : C →* MulAut C).range := by
    rintro ⟨g, hg⟩
    exact hout _ (conj_symm_eq_of_congr_eq_conj e' hg.symm)
  have hφ1 : φ ≠ 1 := fun h => hφout (h ▸ one_mem _)
  have hφord : orderOf φ = p := orderOf_eq_prime hφp hφ1
  obtain ⟨-, -, Θ, hΘ, -⟩ := triality_normal_form_data hℓ hf K₃ hK σ hσ
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K₃ hK σ hσ Θ hΘ hp
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
  have hK3 : Nat.card K₃ = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
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
  have hK' : Nat.card K₃ = ℓ ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, hk, -, -, -, hfixJ, hsimpJ, hncJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd hp.two_le hm3 K₃ hK' σ
      hσ' δc hδc
  haveI := hsimpJ
  set δ₀ := fieldActor (t := TwistTag.D4) σ δc with hδ₀
  have e3 : ↥(fixSubgroup δ₀) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K₃ σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K₃ σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hsimE : IsSimpleGroup ↥(fixSubgroup δ₀) := e3.isSimpleGroup
  have hncE : ∃ a b : ↥(fixSubgroup δ₀), a * b ≠ b * a := by
    simp only [not_forall, ne_eq] at hncJ
    obtain ⟨a, b, hab⟩ := hncJ
    refine ⟨e3.symm a, e3.symm b, fun h => hab ?_⟩
    have h' := congrArg e3 h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  haveI : Finite (fixSubfield δc) := Subtype.finite
  have hk3 : Nat.card (fixSubfield δc) = (ℓ ^ f') ^ 3 := by rw [hk, ← pow_mul, mul_comm]
  obtain ⟨r, hr, hσr⟩ := exists_cubic_exponent_exc hp (by omega) (fixSubfield δc) hk σ hσ'
  let q' : TauCeti.PrimePower := ⟨ℓ, f', hℓ, hd⟩
  have hv' : (TauCeti.LieTypeIndex.trialityD4 q').Valid :=
    TauCeti.LieTypeIndex.valid_trialityD4 q'
  have hq'card : q'.card = ℓ ^ f' := TauCeti.PrimePower.card_def q'
  have hKq : Nat.card (fixSubfield δc) = q'.card ^ 3 := by rw [hk3, hq'card]
  set σ₀ := fixSubfieldRestrict σ δc with hσ₀def
  have hσ₀ : ∀ c, σ₀ c = c ^ ((ℓ ^ f') ^ r) := fun c => Subtype.ext (hσr c)
  obtain ⟨σ₁, hσ₁, ⟨eo⟩⟩ : ∃ σ₁ : fixSubfield δc ≃+* fixSubfield δc,
      (∀ c, σ₁ c = c ^ q'.card) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 (fixSubfield δc) σ₀.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 (fixSubfield δc) σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ₀, fun c => by rw [hσ₀, pow_one, hq'card], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ₀.symm c = c ^ q'.card := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ₀, hq'card, ← pow_mul,
          show ℓ ^ f' * (ℓ ^ f') ^ 2 = (ℓ ^ f') ^ 3 by ring]
        have : Fintype (fixSubfield δc) := Fintype.ofFinite _
        have hq : Fintype.card (fixSubfield δc) = (ℓ ^ f') ^ 3 := by
          rw [← Nat.card_eq_fintype_card, hk3]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ₀.symm, h₁,
        CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_inv_D4
          (fixSubfield δc) σ₀ σ₀.symm (fun c => σ₀.apply_symm_apply c)⟩
  obtain ⟨eCat⟩ := catEquiv_trialityD4_of_field q' hv' (fixSubfield δc) hKq σ₁ hσ₁
  let eJ : graphFixedRootGroup TwistTag.D4 (fixSubfield δc) σ₀.toRingHom ≃*
      ↥(trialityFieldImage σ δc) :=
    Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δc).subtype)
      (baseChangeGL_injective _)
  let eN : ↥(fixSubgroup δ₀) ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hv'⟩).Group :=
    ((e3.trans eJ.symm).trans eo).trans eCat.symm
  have hder : ⁅fixSubgroup δ₀, fixSubgroup δ₀⁆ = fixSubgroup δ₀ :=
    Subgroup.isPerfect_iff.1 ⟨(b3Lie_isQuasisimple_of_simple hncE).1⟩
  have hδ₀ : FixCompsEquiv δ₀ (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hv'⟩).Group :=
    fixCompsEquiv_of_derived_eq_simple hder hsimE hncE eN
  have hβc : FixCompsEquiv β (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hv'⟩).Group := by
    refine FixCompsEquiv.of_congr e' (FixCompsEquiv.of_conj (MulAut.conj h₀) ?_)
    rw [← hφdef, hh₀']
    exact FixCompsEquiv.of_fixSubgroup_eq hfix_eq.symm hδ₀
  have hZT : Subgroup.center (TauCeti.CFSGIndex.lie ⟨.trialityD4 q', hv'⟩).Group = ⊥ := by
    have h1 := Subgroup.map_center_eq eN
    rw [b3Lie_center_eq_bot hncE, Subgroup.map_bot] at h1
    exact h1.symm
  refine ⟨hβc.center_eq_bot hZT hJ, q', hv', ?_, hβc J hJ⟩
  rw [hq'card, ← pow_mul, TauCeti.PrimePower.card_def, ← hfdef, hff', mul_comm]

end CFSG.LocalAnalysis.GLTheoremA.S2019
