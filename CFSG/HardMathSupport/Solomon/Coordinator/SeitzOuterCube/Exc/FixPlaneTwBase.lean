module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti

theorem exists_primePower_fixSubfield_twisted {q : PrimePower} {m : ℕ} (hm : 0 < m) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = q.card ^ m) (η : K ≃+* K) {p : ℕ} (hp : p.Prime)
    (hpm : ¬ p ∣ m) (hη : orderOf η = p) :
    ∃ q₀ : PrimePower, q₀.p = q.p ∧ q.card = q₀.card ^ p ∧
      Nat.card (fixSubfield η) = q₀.card ^ m := by
  have hK' : Nat.card K = q.p ^ (q.exponent * m) := by
    rw [hK, PrimePower.card_def, ← pow_mul]
  obtain ⟨hdvd, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield q.prime_p
      (Nat.mul_pos q.exponent_pos hm) hK' η
  rw [hη] at hdvd hcard
  have hpe : p ∣ q.exponent := (Nat.Coprime.dvd_of_dvd_mul_right
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm) hdvd)
  obtain ⟨k, hk⟩ := hpe
  have hkpos : 0 < k := by
    have := q.exponent_pos
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk
      omega
    · exact h
  refine ⟨⟨q.p, k, q.prime_p, hkpos⟩, rfl, ?_, ?_⟩
  · rw [PrimePower.card_def q, PrimePower.card_def ⟨q.p, k, q.prime_p, hkpos⟩, ← pow_mul, hk,
      mul_comm]
  · rw [hcard, PrimePower.card_def ⟨q.p, k, q.prime_p, hkpos⟩, ← pow_mul,
      show q.exponent * m = p * (k * m) by rw [hk]; ring, Nat.mul_div_cancel_left _ hp.pos]

section Bridge


theorem catEquiv_graphFixedRootGroup_of_data (t : TwistTag) {c : PrimePower → LieTypeIndex}
    (hB : Even.TwistedBridgeAll t c) (q : PrimePower) (hv : (c q).Valid) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = q.card ^ t.order) (σ : K ≃+* K)
    (hσ : ∀ x, σ x = x ^ q.card) :
    Nonempty (Cat ⟨c q, hv⟩ ≃* ↥(graphFixedRootGroup t K σ.toRingHom)) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK' : Nat.card K = (q.p ^ q.exponent) ^ t.order := by rw [hK, PrimePower.card_def]
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ, PrimePower.card_def]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact hσ x
  obtain ⟨φ⟩ := hB q hv K hK σ.toRingHom hσ'
  have hperf := finite_fixed_root_group_perfect t q.prime_p q.exponent_pos K hK' σ.toRingHom hσ''
  have hZ : Subgroup.center ↥(graphFixedRootGroup t K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv _ _ hperf.2.2.1 hZ
  exact ⟨φ.symm.trans ψ⟩

theorem fixPlaneGen_tw_of_data (hLow : ExcInnerLowPlanes) (t : TwistTag)
    {c : PrimePower → LieTypeIndex} (hnc : ∀ q, ¬ IsClassicalIndex (c q))
    (hex : ∀ q p, ¬ IsD2SeitzException p (c q)) (hchar : ∀ q, (c q).characteristic = q.p)
    (hinj : ∀ (q : PrimePower) (hv : (c q).Valid),
      Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)))
    {q : PrimePower} {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ≠ q.p) (hrank : RankLE2 p ↥(graphFixedRootGroup t K σ.toRingHom))
    (hdesc : ∀ α : MulAut ↥(graphFixedRootGroup t K σ.toRingHom), IsOuterOfOrder p α →
      ∃ (ψ : MulAut ↥(graphFixedRootGroup t K σ.toRingHom)) (η : K ≃+* K), orderOf η = p ∧
        ψ * α * ψ⁻¹ = fieldActor (t := t) σ η)
    (hfix : ∀ η : K ≃+* K, orderOf η = p → ∃ (q₀ : PrimePower) (hv₀ : (c q₀).Valid),
      q₀.p = q.p ∧ Nonempty (↥(fixedSubgroup (fieldActor (t := t) σ η)) ≃* Cat ⟨c q₀, hv₀⟩)) :
    FixPlaneGen ↥(graphFixedRootGroup t K σ.toRingHom) p := by
  refine fixPlaneGen_of_standard_cat ⊤
    {g | ∃ η : K ≃+* K, orderOf η = p ∧ g = fieldActor (t := t) σ η} ?_ ?_
  · intro α hα
    obtain ⟨ψ, η, hη, h⟩ := hdesc α hα
    refine ⟨ψ⁻¹, Subgroup.mem_top _, fieldActor (t := t) σ η, ⟨η, hη, rfl⟩, ?_⟩
    rw [← h]
    group
  · rintro _ ⟨η, hη, rfl⟩
    obtain ⟨q₀, hv₀, hq₀p, ⟨e⟩⟩ := hfix η hη
    refine ⟨Cat ⟨c q₀, hv₀⟩, inferInstance, e, ?_⟩
    intro B hBa hBc
    exact closure_centralizers_of_excInnerLow hLow (hnc q₀) hp hp2
      (by show p ≠ (c q₀).characteristic; rw [hchar, hq₀p]; exact hpq) (hex q₀ p)
      (hinj q₀ hv₀) (rankLE2_of_equiv_fixed e hrank) B hBa hBc

end Bridge

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
