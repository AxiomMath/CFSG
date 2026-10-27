module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPFamilies
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.NotA6

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.DefCharOuter.Export CFSG.Yardstones.Md0ec50421ce4

set_option linter.unusedSectionVars false

theorem pow_pow_add_mul_eq_of_card_exc {k : Type*} [Field k] [Finite k] {ℓ m : ℕ}
    (hk : Nat.card k = ℓ ^ m) (a b : ℕ) (c : k) : c ^ ℓ ^ (m * a + b) = c ^ ℓ ^ b := by
  have : Fintype k := Fintype.ofFinite k
  have hq : Fintype.card k = ℓ ^ m := by rw [← Nat.card_eq_fintype_card, hk]
  have he : ℓ ^ (m * a + b) = (ℓ ^ m) ^ a * ℓ ^ b := by rw [pow_add, pow_mul]
  rw [he, pow_mul, ← hq, FiniteField.pow_card_pow]

theorem exists_cubic_exponent_exc {ℓ p f' : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {K : Type} [Field K]
    (K₀ : Subfield K) [Finite K₀] (hk : Nat.card K₀ = ℓ ^ (3 * f')) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ ℓ ^ (f' * p)) :
    ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ ∀ c : K₀, σ (c : K) = ((c ^ ((ℓ ^ f') ^ r) : K₀) : K) := by
  have hp3' : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
      omega
    omega
  refine ⟨p % 3, hp3', fun c => ?_⟩
  have hpe : f' * p = 3 * f' * (p / 3) + f' * (p % 3) := by
    have := Nat.div_add_mod p 3
    nlinarith [this]
  have h1 := pow_pow_add_mul_eq_of_card_exc (ℓ := ℓ) (m := 3 * f') (k := K₀) hk (p / 3)
    (f' * (p % 3)) c
  rw [← hpe] at h1
  rw [hσ, SubmonoidClass.coe_pow, ← pow_mul]
  have h2 := congrArg Subtype.val h1
  rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow] at h2
  exact h2

section TriD4


theorem isChevSimple_graphFixedRootGroup_cubic_exc {ℓ f' : ℕ} (hℓ : ℓ.Prime) (hf' : 1 ≤ f')
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f') ^ 3) (σ : K ≃+* K) {r : ℕ}
    (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((ℓ ^ f') ^ r)) :
    IsChevSimple ℓ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      IsEmpty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* alternatingGroup (Fin 6)) := by
  classical
  let q' : TauCeti.PrimePower := ⟨ℓ, f', hℓ, hf'⟩
  have hv' : (TauCeti.LieTypeIndex.trialityD4 q').Valid := TauCeti.LieTypeIndex.valid_trialityD4 q'
  have hKq : Nat.card K = q'.card ^ 3 := by rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨σ₁, hσ₁, ⟨e⟩⟩ : ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ q'.card) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ, fun c => by rw [hσ, pow_one, TauCeti.PrimePower.card_def], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ.symm c = c ^ q'.card := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ, TauCeti.PrimePower.card_def, ← pow_mul,
          show ℓ ^ f' * (ℓ ^ f') ^ 2 = (ℓ ^ f') ^ 3 by ring]
        have : Fintype K := Fintype.ofFinite K
        have hq : Fintype.card K = (ℓ ^ f') ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ.symm, h₁, exists_mulEquiv_graphFixedRootGroup_inv_D4 K σ σ.symm
        (fun c => σ.apply_symm_apply c)⟩
  obtain ⟨eCat⟩ := catEquiv_trialityD4_of_field q' hv' K hKq σ₁ hσ₁
  have hchev : IsChevSimple ℓ (graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) :=
    isChevSimple_of_lie (q := ℓ) ⟨.trialityD4 q', hv'⟩
      (TauCeti.LieTypeIndex.characteristic_trialityD4 q') eCat.symm
  have hA6 : IsEmpty (graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom ≃*
      alternatingGroup (Fin 6)) :=
    ⟨fun f => (isEmpty_cat_alt6 ⟨.trialityD4 q', hv'⟩ (Or.inl rfl)).false (eCat.trans f)⟩
  exact ⟨isChevSimple_congr e.symm hchev, ⟨fun f => hA6.false (e.symm.trans f)⟩⟩

theorem trialityFieldExportP {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : TrialityFieldExportP p := by
  intro ℓ f hℓ' hf K _ _ hK σ hσ φ hφp hφout
  classical
  have hℓ : ℓ.Prime := hℓ'.out
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
  obtain ⟨-, -, hk, -, -, -, hfixJ, hsimpJ, hncJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd hp.two_le hm3 K hK' σ
      hσ' δc hδc
  haveI := hsimpJ
  set δ₀ := fieldActor (t := TwistTag.D4) σ δc with hδ₀
  have e3 : ↥(fixSubgroup δ₀) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
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
  obtain ⟨hG₀, hG₀A6⟩ := isChevSimple_graphFixedRootGroup_cubic_exc hℓ hd (fixSubfield δc) hk3
    (fixSubfieldRestrict σ δc) hr fun c => Subtype.ext (hσr c)
  have eJ : graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom ≃* ↥(trialityFieldImage σ δc) :=
    Subgroup.equivMapOfInjective _ (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield δc).subtype)
      (baseChangeGL_injective _)
  have eM : ↥(fixSubgroup δ₀) ≃* graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom := e3.trans eJ.symm
  have hchevE : IsChevSimple ℓ ↥(fixSubgroup δ₀) := isChevSimple_congr eM.symm hG₀
  have hA6E : IsEmpty ((↥(fixSubgroup δ₀) ⧸ Subgroup.center ↥(fixSubgroup δ₀)) ≃*
      alternatingGroup (Fin 6)) :=
    isEmpty_quotient_center_alt6 (b3Lie_center_eq_bot hncE)
      ⟨fun f => hG₀A6.false (eM.symm.trans f)⟩
  have hperf : commutator ↥(fixSubgroup δ₀) = ⊤ := (b3Lie_isQuasisimple_of_simple hncE).1
  have hder : ⁅fixSubgroup δ₀, fixSubgroup δ₀⁆ = fixSubgroup δ₀ :=
    Subgroup.isPerfect_iff.1 ⟨hperf⟩
  haveI : Finite ↥(fixSubgroup δ₀) := Subtype.finite
  have hexp : LieCompExport ℓ δ₀ := by
    refine lieCompExport_of_derived_eq_simple hder hsimE hncE
      ⟨↥(fixSubgroup δ₀), inferInstance, inferInstance, lieFactorData_of_simple hncE hchevE,
        MonoidHom.id _, Function.surjective_id, ?_⟩ hA6E
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [show x = 1 from hx]
    exact one_mem _
  have hexp' : LieCompExport ℓ (fieldActor (t := TwistTag.D4) σ (Θ φ)) :=
    lieCompExport_of_fixSubgroup_eq hfix_eq.symm hexp
  exact (lieCompExport_of_conj (MulAut.conj h₀) φ (by rw [hh₀']; exact hexp')).toComps

end TriD4

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
