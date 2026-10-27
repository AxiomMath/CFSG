module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55D4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55D4ThreeFix
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55D4ThreeSyl
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeNF

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.ClassicalInvolution.G2D4Models
  CFSG.LieType.Steinberg.TwistedD4
open scoped Pointwise

theorem mulAut_mul_conj_inv' {Y : Type} [Group Y] (δ : MulAut Y) (g : Y) :
    δ * (MulAut.conj g)⁻¹ = MulAut.conj (δ g⁻¹) * δ := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.mul_apply, map_mul, map_inv]

section Three


abbrev D4G (K : Type) [Field K] (σ : K ≃+* K) : Type :=
  ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

theorem outerFalse_d4_three_native {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) :
    OuterFalse 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  intro α hαinn hα3 hS hHH
  obtain ⟨S, hS⟩ := hS
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨-, -, ⟨Θ, hΘ, -, hΘker, -⟩, -, -, -, hcen, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Φ : MulAut (D4G K σ) := fieldActor (t := TwistTag.D4) σ σ with hΦdef
  have hq : Odd (3 ^ f) := (by decide : Odd 3).pow
  have hK3 : Nat.card K = 3 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 3 := finite_field_prime_power_characteristic hp (by omega) hK3
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hσ1 : σ ≠ 1 := by
    intro h
    have h3 : 3 * f ∣ f := CFSG.GH74.GLS.Stage2.Bender.Thm1.dvd_of_forall_pow_prime_pow_eq hp K
        hK3 (fun x => by
      have := hσ x
      rw [h] at this
      exact this.symm)
    have := Nat.le_of_dvd (by omega) h3
    omega
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hΦ3 : Φ ^ 3 = 1 := by
    have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
    rw [hσ3, map_one] at h
    exact h.symm
  have hΘΦ : Θ Φ = σ := hΘ Φ 1 σ (by rw [map_one, one_mul])
  have hker : ∀ φ : MulAut (D4G K σ), Θ φ = 1 ↔
      φ ∈ (MulAut.conj : D4G K σ →* MulAut (D4G K σ)).range := by
    intro φ
    rw [← hΘker, MonoidHom.mem_ker]
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact hαinn ⟨1, map_one MulAut.conj⟩
  have hord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  obtain ⟨g, -, hφ⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.d4_outer_three_normal_form hp hp2 hf K hK
    σ hσ α hord hαinn
  obtain ⟨β, hβα, hβg, hβ3, hβS⟩ : ∃ β : MulAut (D4G K σ), (β = α ∨ β = α⁻¹) ∧
      (∃ g : D4G K σ, β = MulAut.conj g * Φ) ∧ β ^ 3 = 1 ∧ ∀ s ∈ S, β s = s := by
    rcases hφ with hφ | hφ
    · exact ⟨α, Or.inl rfl, ⟨g, hφ⟩, hα3, hS⟩
    · refine ⟨α⁻¹, Or.inr rfl, ⟨g, hφ⟩, by rw [inv_pow, hα3, inv_one], fun s hs => ?_⟩
      have h := hS s hs
      calc α⁻¹ s = α⁻¹ (α s) := by rw [h]
        _ = s := α.symm_apply_apply s
  obtain ⟨g₁, hg₁⟩ := hβg
  have hD4 : D4Data K σ.toRingHom (3 ^ f) :=
    ⟨hq, hK, fun c => hσ c⟩
  obtain ⟨E, hE2, hEfix, hEcent⟩ := exists_fixed_two_subgroup (σ := σ.toRingHom) hD4.sigma3 hD4
  have hrange : (twistedIncl σ.toRingHom).range =
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := hD4.range
  let eT : twistedGroup σ.toRingHom →* D4G K σ :=
    (twistedIncl σ.toRingHom).codRestrict (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) hD4.hgF
  have heTinj : Function.Injective eT := by
    intro x y hxy
    have h : twistedIncl σ.toRingHom x = twistedIncl σ.toRingHom y :=
      congrArg (fun z : D4G K σ => (z : ModGL TwistTag.D4.tag K)) hxy
    exact twistedIncl_injective σ.toRingHom h
  have heTsurj : Function.Surjective eT := by
    intro x
    have hx : (x : ModGL TwistTag.D4.tag K) ∈ (twistedIncl σ.toRingHom).range := by
      rw [hrange]
      exact x.2
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  let E' : Subgroup (D4G K σ) := E.map eT
  have hE'2 : IsPGroup 2 E' := hE2.map eT
  have hE'Φ : ∀ e ∈ E', Φ e = e := by
    rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    rw [hΦdef, coe_fieldActor]
    exact hEfix x hx
  have hE'cent : ∀ y : D4G K σ, (∀ e ∈ E', y * e = e * y) → y ^ 3 = 1 → y = 1 := by
    intro y hy hy3
    obtain ⟨x, rfl⟩ := heTsurj y
    have hx : ∀ e ∈ E, x * e = e * x := by
      intro e he
      apply heTinj
      rw [map_mul, map_mul]
      exact hy (eT e) ⟨e, he, rfl⟩
    have hx3 : x ^ 3 = 1 := by
      apply heTinj
      rw [map_pow, hy3, map_one]
    have := hEcent x hx hx3
    rw [this, map_one]
  obtain ⟨Q, hQ⟩ := hE'2.exists_le_sylow
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq (D4G K σ) S Q
  have hE'S : ∀ e ∈ E', ∃ s ∈ S, MulAut.conj g₀ s = e := by
    intro e he
    have h1 : e ∈ (Q : Subgroup (D4G K σ)) := hQ he
    rw [← hg₀, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨s, hs, hse⟩ := h1
    exact ⟨s, hs, hse⟩
  set β' : MulAut (D4G K σ) := MulAut.conj g₀ * β * (MulAut.conj g₀)⁻¹ with hβ'
  have hβ'E : ∀ e ∈ E', β' e = e := by
    intro e he
    obtain ⟨s, hs, rfl⟩ := hE'S e he
    simp only [hβ', MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hβS s hs]
  have hβ'3 : β' ^ 3 = 1 := by
    have : β' ^ 3 = MulAut.conj g₀ * β ^ 3 * (MulAut.conj g₀)⁻¹ := by
      rw [hβ']
      exact conj_pow
    rw [this, hβ3]
    group
  have hβ'g : β' = MulAut.conj (g₀ * g₁ * Φ g₀⁻¹) * Φ := by
    calc β' = MulAut.conj g₀ * (MulAut.conj g₁ * Φ) * (MulAut.conj g₀)⁻¹ := by rw [hβ', hg₁]
      _ = MulAut.conj g₀ * MulAut.conj g₁ * (Φ * (MulAut.conj g₀)⁻¹) := by group
      _ = MulAut.conj g₀ * MulAut.conj g₁ * (MulAut.conj (Φ g₀⁻¹) * Φ) := by
        rw [mulAut_mul_conj_inv']
      _ = MulAut.conj (g₀ * g₁ * Φ g₀⁻¹) * Φ := by simp only [map_mul, mul_assoc]
  have hΘord : orderOf (Θ Φ) = 3 := by rw [hΘΦ]; exact hσord
  obtain ⟨y, k, hk, hβ'eq⟩ := exists_conj_of_fixing Θ hker hcen hΘord hΦ3 _ hβ'g hβ'3 E'
    hE'Φ hβ'E hE'cent
  have hβeq : β = MulAut.conj (g₀⁻¹ * y) * Φ ^ k * (MulAut.conj (g₀⁻¹ * y))⁻¹ := by
    have : β = (MulAut.conj g₀)⁻¹ * β' * MulAut.conj g₀ := by rw [hβ']; group
    rw [this, hβ'eq, map_mul, map_inv]
    group
  obtain ⟨h₀, m, hm, hαeq⟩ : ∃ (h₀ : D4G K σ) (m : ℕ), (m = 1 ∨ m = 2) ∧
      α = MulAut.conj h₀ * Φ ^ m * (MulAut.conj h₀)⁻¹ := by
    rcases hβα with rfl | hβα
    · exact ⟨g₀⁻¹ * y, k, hk, hβeq⟩
    · refine ⟨g₀⁻¹ * y, 3 - k, by omega, ?_⟩
      have hα' : α = β⁻¹ := by rw [hβα]; group
      have hk3 : k ≤ 3 := by omega
      have hΦk : (Φ ^ k)⁻¹ = Φ ^ (3 - k) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_add, Nat.add_sub_cancel' hk3, hΦ3]
      rw [hα', hβeq, mul_inv_rev, mul_inv_rev, inv_inv, hΦk, mul_assoc]
  have hunits : Nat.card Kˣ = (3 ^ f) ^ 3 - 1 := by rw [Nat.card_units, hK]
  have hq03 : 3 ≤ 3 ^ f := Nat.le_self_pow (by omega) 3
  obtain ⟨r, hr, hr2, hr3, hrdvd, hrnd⟩ := exists_prime_dvd_pow_sub_one_not_dvd hp hp2
    (dvd_pow_self 3 (by omega)) hq03 hq
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r (hunits ▸ hrdvd)
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h3K : (3 : K) = 0 := by
      have := CharP.cast_eq_zero K 3
      simpa using this
    exact one_ne_zero (by linear_combination h3K - h)
  have hot : orderOf (d4Tor σ hK hσ c) = r := by
    rw [orderOf_injective (d4Tor σ hK hσ) (d4Tor_injective σ hK hσ h2) c]
    exact hc
  have hσpow : ∀ (n : ℕ) (x : K), (σ ^ n) x = x ^ ((3 ^ f) ^ n) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hσ, ih, ← pow_mul, ← pow_succ']
  have hΦm : Φ ^ m = fieldActor σ (σ ^ m) := by
    have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ m
    exact h.symm
  have hηc : Units.map (σ ^ m).toRingHom.toMonoidHom c = c ^ ((3 ^ f) ^ m) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hσpow m c
  have hft : fieldActor σ (σ ^ m) (d4Tor σ hK hσ c) = (d4Tor σ hK hσ c) ^ ((3 ^ f) ^ m) := by
    rw [fieldActor_d4Tor, hηc, map_pow]
  have hcq : c ^ (3 ^ f) = c → False := by
    intro h
    have hpos : 0 < 3 ^ f := by positivity
    have h' : c ^ (3 ^ f - 1) = 1 := by
      have : c ^ (3 ^ f - 1) * c = 1 * c := by
        rw [← pow_succ, Nat.sub_add_cancel hpos, one_mul]
        exact h
      exact mul_right_cancel this
    exact hrnd (hc ▸ orderOf_dvd_of_pow_eq_one h')
  have hne : fieldActor σ (σ ^ m) (d4Tor σ hK hσ c) ≠ d4Tor σ hK hσ c := by
    intro h
    rw [fieldActor_d4Tor] at h
    have h1 : Units.map (σ ^ m).toRingHom.toMonoidHom c = c := d4Tor_injective σ hK hσ h2 h
    rw [hηc] at h1
    rcases hm with rfl | rfl
    · exact hcq (by simpa using h1)
    · apply hcq
      have hcpow : c ^ ((3 ^ f) ^ 3 - 1) = 1 := by
        have := pow_card_eq_one' (G := Kˣ) (x := c)
        rwa [Nat.card_units, hK] at this
      have hpos : 0 < (3 ^ f) ^ 3 := by positivity
      have h3 : c ^ ((3 ^ f) ^ 3) = c := by
        calc c ^ ((3 ^ f) ^ 3) = c ^ ((3 ^ f) ^ 3 - 1) * c := by
              rw [← pow_succ, Nat.sub_add_cancel hpos]
          _ = c := by rw [hcpow, one_mul]
      have h4 : c ^ ((3 ^ f) ^ 3) = c ^ (3 ^ f) := by
        have hexp : (3 ^ f) ^ 3 = (3 ^ f) ^ 2 * 3 ^ f := by ring
        calc c ^ ((3 ^ f) ^ 3) = c ^ ((3 ^ f) ^ 2 * 3 ^ f) := by rw [hexp]
          _ = (c ^ ((3 ^ f) ^ 2)) ^ (3 ^ f) := pow_mul c _ _
          _ = c ^ (3 ^ f) := by rw [h1]
      exact h4.symm.trans h3
  have hα' : α = MulAut.conj h₀ * fieldActor σ (σ ^ m) * (MulAut.conj h₀)⁻¹ := by
    rw [hαeq, hΦm]
  exact false_of_torus_moved_pow hα' hr hr2 hr3 hot hft hne hHH

end Three

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
