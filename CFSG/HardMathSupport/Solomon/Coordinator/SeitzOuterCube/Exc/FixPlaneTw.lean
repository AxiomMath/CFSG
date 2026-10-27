module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TwE6Fixed
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TrialityFixed
public import CFSG.HardMathSupport.Lang.E6Descent.FieldAutTwE6
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti


section TwE6



theorem fixSubfieldRestrict_eq_pow_twE6 {q q₀ : PrimePower} {p : ℕ} (hqq : q.card = q₀.card ^ p)
    (hp : Odd p) {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ q.card)
    (η : K ≃+* K) (hF : Nat.card (fixSubfield η) = q₀.card ^ 2) :
    ∀ x : ↥(fixSubfield η), fixSubfieldRestrict σ η x = x ^ q₀.card := by
  intro x
  have : Fintype (fixSubfield η) := Fintype.ofFinite _
  have hc : Fintype.card (fixSubfield η) = q₀.card ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  have hpow : ∀ (y : ↥(fixSubfield η)) (n : ℕ), y ^ (q₀.card ^ 2) ^ n = y := fun y n => by
    rw [← hc]
    exact FiniteField.pow_card_pow n y
  obtain ⟨k, hk⟩ := hp
  have hxp : x ^ q₀.card ^ p = x ^ q₀.card := by
    rw [hk, show q₀.card ^ (2 * k + 1) = q₀.card * (q₀.card ^ 2) ^ k by ring, pow_mul]
    exact hpow _ k
  apply Subtype.ext
  rw [coe_fixSubfieldRestrict, hσ, hqq, ← SubmonoidClass.coe_pow, hxp]

theorem twE6_fixedSubgroup_equiv_cat {q q₀ : PrimePower} {p : ℕ} (hqq : q.card = q₀.card ^ p)
    (hp : p.Prime) (hp3 : 3 < p) {K : Type} [Field K] [Finite K] (hK : Nat.card K = q.card ^ 2)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ q.card) {η : K ≃+* K} (hη : orderOf η = p)
    (hF : Nat.card (fixSubfield η) = q₀.card ^ 2) (hv₀ : (LieTypeIndex.twistedE6 q₀).Valid) :
    Nonempty (↥(fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)) ≃* Cat ⟨.twistedE6 q₀, hv₀⟩) := by
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 2 := by rw [hK, PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [hσ, PrimePower.card_def]
  obtain ⟨e₁⟩ := twE6_fixedSubgroup_equiv_subfield q.prime_p q.exponent_pos hK' σ hσ' hp hp3 hη
  obtain ⟨e₂⟩ := catEquiv_graphFixedRootGroup_of_data TwistTag.E6
    Even.chevalleyBridgesAll.twistedE6 q₀ hv₀ (fixSubfield η) hF (fixSubfieldRestrict σ η)
    (fixSubfieldRestrict_eq_pow_twE6 hqq (hp.odd_of_ne_two (by omega)) σ hσ η hF)
  exact ⟨e₁.trans e₂.symm⟩

theorem conj_injective_cat_twE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨.twistedE6 q, hv⟩ →* MulAut (Cat ⟨.twistedE6 q, hv⟩)) := by
  obtain ⟨K, _, σ, -, -, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  exact conj_injective_of_mulEquiv e (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.E6 K σ))

theorem fixPlaneGen_twE6 (hLow : ExcInnerLowPlanes) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card ^ 2) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ q.card)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ≠ q.p)
    (hrank : RankLE2 p ↥(twistedE6RootGroup K σ)) : FixPlaneGen ↥(twistedE6RootGroup K σ) p := by
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 2 := by rw [hK, PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [hσ, PrimePower.card_def]
  have hp2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  refine fixPlaneGen_tw_of_data hLow TwistTag.E6 (c := LieTypeIndex.twistedE6)
    (fun q => (isChevalleyExcIndex_twistedE6 q).not_classical)
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_twistedE6 q))
    (fun q => LieTypeIndex.characteristic_twistedE6 q)
    (fun q hv => conj_injective_cat_twE6 q hv) σ hp (by omega) hpq hrank
    (fun α hα => CFSG.HardMathSupport.Lang.E6Descent.exists_conj_fieldActor_twE6 q.prime_p
      q.exponent_pos hK' σ hσ' hp hp3 α hα) ?_
  intro η hη
  obtain ⟨q₀, hq₀p, hqq, hF⟩ :=
    exists_primePower_fixSubfield_twisted (m := 2) (by norm_num) hK η hp hp2 hη
  exact ⟨q₀, by simp, hq₀p, twE6_fixedSubgroup_equiv_cat hqq hp hp3 hK σ hσ hη hF (by simp)⟩

end TwE6

section Triality


theorem conj_injective_cat_trialityD4 (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) :
    Function.Injective
      (MulAut.conj : Cat ⟨.trialityD4 q, hv⟩ →* MulAut (Cat ⟨.trialityD4 q, hv⟩)) := by
  obtain ⟨K, _, _, hK, -⟩ := exists_field_pow q (m := TwistTag.D4.order) TwistTag.D4.order_pos
  rw [PrimePower.card_def] at hK
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.D4 q.prime_p q.exponent_pos K hK
  have hσ' : ∀ x, σ x = x ^ q.card := fun x => by
    rw [PrimePower.card_def]
    exact hσ x
  have hK3 : Nat.card K = q.card ^ TwistTag.D4.order := by rw [PrimePower.card_def]; exact hK
  obtain ⟨e⟩ := catEquiv_graphFixedRootGroup_of_data TwistTag.D4
    Even.chevalleyBridgesAll.trialityD4 q hv K hK3 σ hσ'
  exact conj_injective_of_mulEquiv e (CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
    (center_graphFixedRootGroup_eq_bot σ.surjective))

theorem trialityD4_stdDescent {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ α : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsOuterOfOrder p α →
      ∃ (ψ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (η : K ≃+* K),
        orderOf η = p ∧ ψ * α * ψ⁻¹ = fieldActor (t := TwistTag.D4) σ η := by
  classical
  intro α hα
  obtain ⟨hord, hout⟩ := hα
  by_cases h2 : ℓ = 2
  · subst h2
    obtain ⟨-, -, ⟨Θ, hΘ, hsurj, hker, -⟩, hcyc, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    obtain ⟨hηord, -, ⟨h₀, hh₀⟩, -⟩ :=
      CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
        Nat.prime_two hf K hK σ hσ Θ hΘ hp (by omega) ⊤ le_top ⟨α, Subgroup.mem_top _⟩
        (fun ⟨g, hg⟩ => hout g hg.symm) (by rw [Subgroup.orderOf_mk]; exact hord)
    exact ⟨MulAut.conj h₀, Θ α, hηord, hh₀⟩
  · obtain ⟨-, -, ⟨Θ, hΘ, hsurj, hker, -⟩, hcyc, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ h2 hf K hK σ hσ
    obtain ⟨hηord, -, ⟨h₀, hh₀⟩, -⟩ :=
      CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
        hℓ hf K hK σ hσ Θ hΘ hp (by omega) ⊤ le_top ⟨α, Subgroup.mem_top _⟩
        (fun ⟨g, hg⟩ => hout g hg.symm) (by rw [Subgroup.orderOf_mk]; exact hord)
    exact ⟨MulAut.conj h₀, Θ α, hηord, hh₀⟩


theorem fixPlaneGen_trialityD4 (hLow : ExcInnerLowPlanes) {q : PrimePower} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = q.card ^ 3) (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ q.card)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ≠ q.p)
    (hrank : RankLE2 p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    FixPlaneGen ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) p := by
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ 3 := by rw [hK, PrimePower.card_def]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by
    rw [hσ, PrimePower.card_def]
  have hp3 : ¬ p ∣ 3 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h
    omega
  refine fixPlaneGen_tw_of_data hLow TwistTag.D4 (c := LieTypeIndex.trialityD4)
    (fun q => (isChevalleyExcIndex_trialityD4 q).not_classical)
    (fun q p => not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_trialityD4 q))
    (fun q => LieTypeIndex.characteristic_trialityD4 q)
    (fun q hv => conj_injective_cat_trialityD4 q hv) σ hp (by omega) hpq hrank
    (trialityD4_stdDescent q.prime_p q.exponent_pos hK' σ hσ' hp hp5) ?_
  intro η hη
  obtain ⟨q₀, hq₀p, hqq, hF⟩ :=
    exists_primePower_fixSubfield_twisted (m := 3) (by norm_num) hK η hp hp3 hη
  exact ⟨q₀, by simp, hq₀p, trialityD4_fixedSubgroup_equiv_cat hqq hp hp5 hK σ hσ hη hF
    (by simp)⟩

end Triality

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
