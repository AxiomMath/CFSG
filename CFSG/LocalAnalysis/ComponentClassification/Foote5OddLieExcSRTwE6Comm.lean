module

public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRTwE6

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem compatDiag_pow_three_mem_inner {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (w : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    compatDiagAutHom TwistTag.E6 K σ.toRingHom w ^ 3 ∈ twistedE6Inn K σ := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨_Θ, -, -, -, -, h3, -⟩, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hmem : compatDiagAutHom TwistTag.E6 K σ.toRingHom w ∈
      twistedE6Inn K σ ⊔ twistedE6Diag K σ := Subgroup.mem_sup_right ⟨w, rfl⟩
  have h := h3 (QuotientGroup.mk ⟨_, hmem⟩)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
  exact h

theorem compatDiag_map_mul_inv_mem_inner {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) {δ : K ≃+* K} (hδ : Odd (orderOf δ))
    (v : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) :
    compatDiagAutHom TwistTag.E6 K σ.toRingHom
        (orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ δ) v) *
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom v)⁻¹ ∈ twistedE6Inn K σ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set Δ := compatDiagAutHom TwistTag.E6 K σ.toRingHom with hΔ
  have hcube : ∀ w, Δ (w ^ 3) ∈ twistedE6Inn K σ := fun w => by
    rw [map_pow]
    exact compatDiag_pow_three_mem_inner hp hp2 hf hK σ hσ w
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hφord, hgen, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
      (by omega : 1 ≤ 2 * f) hK'
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.1 (by rw [hφord]; omega)
  obtain ⟨j, hj⟩ := hδ
  set ε := δ ^ (j + 1) with hε
  have hεε : ε * ε = δ := by
    rw [hε, ← pow_add, show j + 1 + (j + 1) = orderOf δ + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hεφ : ε ∈ Submonoid.powers φ := hφfin.mem_powers_iff_mem_zpowers.2 (by
    rw [hgen]
    exact Subgroup.mem_top ε)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 hεφ
  have hδc : ∀ c : K, δ c = c ^ (p ^ k * p ^ k) := fun c => by
    rw [← hεε, RingAut.mul_apply, ← hk, ringAut_pow_apply_of_frobenius hφ,
      ringAut_pow_apply_of_frobenius hφ, ← pow_mul]
  have hδv : ∀ N : ℕ, (∀ c : K, δ c = c ^ N) →
      orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ δ) v = v ^ N := by
    intro N hN
    funext a
    refine Units.ext (Subtype.ext ?_)
    change δ ((v a : orbitField TwistTag.E6 K σ.toRingHom a) : K) =
      (((v ^ N) a : orbitField TwistTag.E6 K σ.toRingHom a) : K)
    rw [hN, Pi.pow_apply, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow]
  by_cases hp3 : p = 3
  ·
    subst hp3
    have hv : ∀ w : (a : Fin TwistTag.E6.foldedTag.rank) →
        (orbitField TwistTag.E6 K σ.toRingHom a)ˣ, Δ w ∈ twistedE6Inn K σ := by
      intro w
      have hw : (w ^ (3 ^ (2 * f - 1))) ^ 3 = w := by
        rw [← pow_mul, ← pow_succ, show 2 * f - 1 + 1 = 2 * f by omega]
        funext a
        refine Units.ext (Subtype.ext ?_)
        rw [Pi.pow_apply, Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, ← hK',
          Nat.card_eq_fintype_card, FiniteField.pow_card]
      rw [← hw]
      exact hcube _
    exact mul_mem (hv _) (inv_mem (hv v))
  ·
    have h3 : ¬ 3 ∣ p ^ k := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    have hmod : (p ^ k * p ^ k) % 3 = 1 := by
      rw [Nat.mul_mod]
      have : p ^ k % 3 = 1 ∨ p ^ k % 3 = 2 := by omega
      rcases this with h | h <;> rw [h]
    generalize p ^ k * p ^ k = N at hmod hδc
    obtain ⟨m, hm⟩ : ∃ m, N = 3 * m + 1 := ⟨N / 3, by omega⟩
    rw [hδv _ hδc, hm, pow_succ, map_mul, mul_inv_cancel_right, pow_mul']
    exact hcube _

theorem commutator_mem_range_conj_twistedE6 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (a b : MulAut (twistedE6RootGroup K σ))
    (ha : Odd (orderOf a)) (hb : Odd (orderOf b)) :
    a * b * a⁻¹ * b⁻¹ ∈
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
  classical
  obtain ⟨-, -, -, -, -, -, -, hNF, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨g₁, u₁, δ₁, rfl⟩ := hNF a
  obtain ⟨g₂, u₂, δ₂, rfl⟩ := hNF b
  have hδ₁ : Odd (orderOf δ₁) := by
    have h := orderOf_map_dvd Θ
      (MulAut.conj g₁ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u₁ * fieldActor σ δ₁)
    rw [hΘ _ g₁ u₁ δ₁ rfl] at h
    exact Odd.of_dvd_nat ha h
  have hδ₂ : Odd (orderOf δ₂) := by
    have h := orderOf_map_dvd Θ
      (MulAut.conj g₂ * compatDiagAutHom TwistTag.E6 K σ.toRingHom u₂ * fieldActor σ δ₂)
    rw [hΘ _ g₂ u₂ δ₂ rfl] at h
    exact Odd.of_dvd_nat hb h
  set π := QuotientGroup.mk' (twistedE6Inn K σ) with hπ
  set Δ := compatDiagAutHom TwistTag.E6 K σ.toRingHom with hΔ
  have hπg : ∀ g, π (MulAut.conj g) = 1 := fun g =>
    (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  have hc1 : Commute (π (Δ u₁)) (π (Δ u₂)) := Commute.map (by
    change Δ u₁ * Δ u₂ = Δ u₂ * Δ u₁
    rw [← map_mul, ← map_mul, mul_comm u₁ u₂]) π
  have hc2 : Commute (π (fieldActor σ δ₁)) (π (fieldActor σ δ₂)) := Commute.map (by
    change fieldActor σ δ₁ * fieldActor σ δ₂ = fieldActor σ δ₂ * fieldActor σ δ₁
    rw [← fieldActor_mul, ← fieldActor_mul,
      LocalAnalysis.ComponentInitial.ringAut_mul_comm K δ₁ δ₂]) π
  have hc3 : ∀ {δ : K ≃+* K}, Odd (orderOf δ) → ∀ v, Commute (π (fieldActor σ δ)) (π (Δ v)) := by
    intro δ hδ v
    have h1 := fieldActor_mul_compatDiagAutHom (t := TwistTag.E6) σ δ v
    have h2 : π (Δ (orbitUnitsMap σ.toRingHom (ringEquiv_comm_of_finite σ δ) v)) = π (Δ v) := by
      rw [← mul_inv_eq_one, ← map_inv, ← map_mul]
      exact (QuotientGroup.eq_one_iff _).2
        (compatDiag_map_mul_inv_mem_inner hp hp2 hf hK σ hσ hδ v)
    change π (fieldActor σ δ) * π (Δ v) = π (Δ v) * π (fieldActor σ δ)
    rw [← map_mul, h1, map_mul, h2]
  have hc : Commute (π (MulAut.conj g₁ * Δ u₁ * fieldActor σ δ₁))
      (π (MulAut.conj g₂ * Δ u₂ * fieldActor σ δ₂)) := by
    rw [map_mul, map_mul, map_mul, map_mul, hπg, hπg, one_mul, one_mul]
    exact (hc1.mul_right (hc3 hδ₂ u₁).symm).mul_left ((hc3 hδ₁ u₂).mul_right hc2)
  set a := MulAut.conj g₁ * Δ u₁ * fieldActor σ δ₁ with ha'
  set b := MulAut.conj g₂ * Δ u₂ * fieldActor σ δ₂ with hb'
  show a * b * a⁻¹ * b⁻¹ ∈ twistedE6Inn K σ
  rw [← QuotientGroup.eq_one_iff]
  change π (a * b * a⁻¹ * b⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc.eq]
  group

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc.SRTwE6
