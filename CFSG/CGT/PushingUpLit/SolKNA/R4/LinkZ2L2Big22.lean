module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big19
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big10
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big11

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section Std

variable {F : Type} [Field F] [Finite F]

theorem autU_mem_zpowers (σ : F ≃+* F) (ξ : Fˣ) : autU σ ξ ∈ Subgroup.zpowers ξ := by
  apply mem_zpowers_of_pow_orderOf_eq_one
  rw [← autU_pow, pow_orderOf_eq_one, autU_one]

theorem autU_mem_zpowers_of_mem (σ : F ≃+* F) {ξ w : Fˣ} (hw : w ∈ Subgroup.zpowers ξ) :
    autU σ w ∈ Subgroup.zpowers ξ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [autU_zpow]
  exact Subgroup.zpow_mem _ (autU_mem_zpowers σ ξ) n

theorem zpowers_pow_eq_one {K : Type} [Group K] {ψ : K} {m : ℕ} (h : ψ ^ m = 1) {σ : K}
    (hσ : σ ∈ Subgroup.zpowers ψ) : σ ^ m = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
  rw [← zpow_natCast, ← zpow_mul, mul_comm k (m : ℤ), zpow_mul, zpow_natCast, h, one_zpow]

@[expose] noncomputable def stdSylow (ξ : Fˣ) (ψ : F ≃+* F) : Subgroup (PGammaL2 F) where
  carrier := {g | ∃ σ ∈ Subgroup.zpowers ψ, ∃ w ∈ Subgroup.zpowers ξ,
    g = gD w σ ∨ g = gA w σ}
  mul_mem' := by
    rintro _ _ ⟨σ, hσ, w, hw, rfl | rfl⟩ ⟨τ, hτ, w', hw', rfl | rfl⟩
    · rw [gD_mul_gD]
      exact ⟨σ * τ, Subgroup.mul_mem _ hσ hτ, w * autU σ w',
        Subgroup.mul_mem _ hw (autU_mem_zpowers_of_mem σ hw'), Or.inl rfl⟩
    · rw [gD_mul_gA]
      exact ⟨σ * τ, Subgroup.mul_mem _ hσ hτ, w * autU σ w',
        Subgroup.mul_mem _ hw (autU_mem_zpowers_of_mem σ hw'), Or.inr rfl⟩
    · rw [gA_mul_gD]
      exact ⟨σ * τ, Subgroup.mul_mem _ hσ hτ, w * (autU σ w')⁻¹,
        Subgroup.mul_mem _ hw (Subgroup.inv_mem _ (autU_mem_zpowers_of_mem σ hw')), Or.inr rfl⟩
    · rw [gA_mul_gA]
      exact ⟨σ * τ, Subgroup.mul_mem _ hσ hτ, w * (autU σ w')⁻¹,
        Subgroup.mul_mem _ hw (Subgroup.inv_mem _ (autU_mem_zpowers_of_mem σ hw')), Or.inl rfl⟩
  one_mem' := by
    exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, Or.inl gD_one_one.symm⟩
  inv_mem' := by
    rintro _ ⟨σ, hσ, w, hw, rfl | rfl⟩
    · rw [gD_inv]
      exact ⟨σ⁻¹, Subgroup.inv_mem _ hσ, (autU σ⁻¹ w)⁻¹,
        Subgroup.inv_mem _ (autU_mem_zpowers_of_mem σ⁻¹ hw), Or.inl rfl⟩
    · rw [gA_inv]
      exact ⟨σ⁻¹, Subgroup.inv_mem _ hσ, autU σ⁻¹ w,
        autU_mem_zpowers_of_mem σ⁻¹ hw, Or.inr rfl⟩

theorem mem_stdSylow_iff {ξ : Fˣ} {ψ : F ≃+* F} {g : PGammaL2 F} :
    g ∈ stdSylow ξ ψ ↔
      ∃ σ ∈ Subgroup.zpowers ψ, ∃ w ∈ Subgroup.zpowers ξ, g = gD w σ ∨ g = gA w σ :=
  Iff.rfl

theorem gD_mem_stdSylow {ξ : Fˣ} {ψ σ : F ≃+* F} {w : Fˣ} (hσ : σ ∈ Subgroup.zpowers ψ)
    (hw : w ∈ Subgroup.zpowers ξ) : gD w σ ∈ stdSylow ξ ψ :=
  ⟨σ, hσ, w, hw, Or.inl rfl⟩

theorem gA_mem_stdSylow {ξ : Fˣ} {ψ σ : F ≃+* F} {w : Fˣ} (hσ : σ ∈ Subgroup.zpowers ψ)
    (hw : w ∈ Subgroup.zpowers ξ) : gA w σ ∈ stdSylow ξ ψ :=
  ⟨σ, hσ, w, hw, Or.inr rfl⟩

theorem stdSylow_le_mon (ξ : Fˣ) (ψ : F ≃+* F) : stdSylow ξ ψ ≤ monGrp F := by
  rintro g ⟨σ, -, w, -, rfl | rfl⟩
  · exact isMon_gD w σ
  · exact isMon_gA w σ

end Std

section Sylow

variable {F : Type} [Field F] [Finite F] {p f : ℕ}

theorem gD_pow_zpow_eq_one {ξ : Fˣ} {ψ : F ≃+* F} {r e : ℕ} (hξ : ξ ^ 2 ^ r = 1)
    (hψ : ψ ^ 2 ^ e = 1) {σ : F ≃+* F} (hσ : σ ∈ Subgroup.zpowers ψ)
    {w : Fˣ} (hw : w ∈ Subgroup.zpowers ξ) : (gD w σ) ^ 2 ^ (e + r) = 1 := by
  have hσe : σ ^ 2 ^ e = 1 := zpowers_pow_eq_one hψ hσ
  have hnr : nrm σ w (2 ^ e) ∈ Subgroup.zpowers ξ :=
    Subgroup.prod_mem _ fun i _ => autU_mem_zpowers_of_mem (σ ^ i) hw
  have hnrpow : (nrm σ w (2 ^ e)) ^ 2 ^ r = 1 := zpowers_pow_eq_one hξ hnr
  rw [show 2 ^ (e + r) = 2 ^ e * 2 ^ r by rw [pow_add], pow_mul, gD_pow, hσe, gD_one_pow,
    hnrpow, gD_one_one]

theorem isPGroup_stdSylow {ξ : Fˣ} {ψ : F ≃+* F} {r e : ℕ} (hξ : ξ ^ 2 ^ r = 1)
    (hψ : ψ ^ 2 ^ e = 1) : IsPGroup 2 ↥(stdSylow ξ ψ) := by
  intro g
  obtain ⟨σ, hσ, w, hw, hg | hg⟩ := g.2
  · refine ⟨e + r, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, hg]
    exact gD_pow_zpow_eq_one hξ hψ hσ hw
  · refine ⟨e + r + 1, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, hg]
    rw [show 2 ^ (e + r + 1) = 2 * 2 ^ (e + r) by
      rw [show e + r + 1 = (e + r) + 1 by omega, pow_succ, mul_comm]]
    rw [pow_mul, gA_sq]
    exact gD_pow_zpow_eq_one hξ hψ (Subgroup.pow_mem _ hσ 2)
      (Subgroup.mul_mem _ hw (Subgroup.inv_mem _ (autU_mem_zpowers_of_mem σ hw)))

theorem mem_zpowers_of_two_power_order {ξ : Fˣ} {r : ℕ} (hξ : orderOf ξ = 2 ^ r)
    (hc1 : 2 ^ r ∣ Nat.card Fˣ) (hc2 : ¬ 2 ^ (r + 1) ∣ Nat.card Fˣ)
    {w : Fˣ} {M : ℕ} (hw : w ^ 2 ^ M = 1) : w ∈ Subgroup.zpowers ξ := by
  have hdvd : orderOf w ∣ 2 ^ M := orderOf_dvd_of_pow_eq_one hw
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  obtain ⟨m, hm⟩ := hc1
  have hm_odd : Odd m := by
    rw [← Nat.not_even_iff_odd]
    intro hm_even
    apply hc2
    obtain ⟨j, hj⟩ := even_iff_two_dvd.mp hm_even
    refine ⟨j, ?_⟩
    rw [hm, hj, pow_succ]
    ring
  have hdvd2 : orderOf w ∣ Nat.card Fˣ := orderOf_dvd_natCard w
  have hdvd3 : 2 ^ i ∣ 2 ^ r * m := by
    rw [← hi]
    rwa [hm] at hdvd2
  have hcop : Nat.Coprime (2 ^ i) m := (Nat.coprime_two_left.mpr hm_odd).pow_left i
  have hdvd4 : 2 ^ i ∣ 2 ^ r := hcop.dvd_of_dvd_mul_right hdvd3
  have hdvd5 : orderOf w ∣ 2 ^ r := by rw [hi]; exact hdvd4
  have hw2 : w ^ 2 ^ r = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd5
  exact mem_zpowers_of_pow_orderOf_eq_one (by rw [hξ]; exact hw2)

theorem isSylow2In_stdSylow [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h4 : 4 ≤ p ^ f) {ξ : Fˣ} {r : ℕ} (hξ : orderOf ξ = 2 ^ r) (hc1 : 2 ^ r ∣ Nat.card Fˣ)
    (hc2 : ¬ 2 ^ (r + 1) ∣ Nat.card Fˣ) {ψ : F ≃+* F} (hψ : orderOf ψ = 2 ^ padicValNat 2 f) :
    IsSylow2In (stdSylow ξ ψ) (monGrp F) := by
  have hξ' : ξ ^ 2 ^ r = 1 := by rw [← hξ]; exact pow_orderOf_eq_one ξ
  have hψ' : ψ ^ 2 ^ padicValNat 2 f = 1 := by rw [← hψ]; exact pow_orderOf_eq_one ψ
  obtain ⟨hK, -⟩ := field_facts (Fact.out : p.Prime) hp2 hF h4
  haveI : IsCyclic (F ≃+* F) := CFSG.ClassicalInvolution.Q3.TL4.MF163.ringAut_isCyclic F hK
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun τ : F ≃+* F => (τ : F → F)) DFunLike.coe_injective
  refine ⟨stdSylow_le_mon ξ ψ, isPGroup_stdSylow (r := r) (e := padicValNat 2 f) hξ' hψ',
    fun V hVM hV2 hle => le_antisymm ?_ hle⟩
  intro g hg
  obtain ⟨n, hn⟩ := hV2 ⟨g, hg⟩
  have hgn : g ^ 2 ^ n = 1 := by
    have := congrArg (fun x : ↥V => (x : PGammaL2 F)) hn
    simpa [Subgroup.coe_pow] using this
  have hσn : g.right ^ 2 ^ n = 1 := by
    have := congrArg SemidirectProduct.right hgn
    simpa [right_pow] using this
  have hσ : g.right ^ 2 ^ padicValNat 2 f = 1 := ringAut_pow_two_pow_eq_one hF hσn
  have hσmem : g.right ∈ Subgroup.zpowers ψ :=
    mem_zpowers_of_pow_orderOf_eq_one (by rw [hψ]; exact hσ)
  let d : PGammaL2 F := gD 1 g.right
  have hdmem : d ∈ stdSylow ξ ψ := gD_mem_stdSylow hσmem (Subgroup.one_mem _)
  have hdV : d ∈ V := hle hdmem
  have hg'V : g * d⁻¹ ∈ V := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hdV)
  have hg'M : IsMon (g * d⁻¹) := hVM hg'V
  have hg'right : (g * d⁻¹).right = 1 := by
    dsimp only [d]
    rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, gD_right, mul_inv_cancel]
  rcases hg'M with ⟨w, hw⟩ | ⟨w, hw⟩
  · rw [hg'right] at hw
    have hwV : gD w 1 ∈ V := by rw [← hw]; exact hg'V
    obtain ⟨M, hM⟩ := hV2 ⟨gD w 1, hwV⟩
    have hM' : (gD w 1) ^ 2 ^ M = 1 := by
      have := congrArg (fun x : ↥V => (x : PGammaL2 F)) hM
      simpa [Subgroup.coe_pow] using this
    have hwM : w ^ 2 ^ M = 1 := by
      rw [gD_one_pow, ← gD_one_one] at hM'
      exact (gD_eq_iff.mp hM').1
    have hwmem : w ∈ Subgroup.zpowers ξ := mem_zpowers_of_two_power_order hξ hc1 hc2 hwM
    have hg'dS : g * d⁻¹ ∈ stdSylow ξ ψ := by
      rw [hw]; exact gD_mem_stdSylow (Subgroup.one_mem _) hwmem
    have h1 : (g * d⁻¹) * d ∈ stdSylow ξ ψ := Subgroup.mul_mem _ hg'dS hdmem
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h1
  · rw [hg'right] at hw
    let ι₀ : PGammaL2 F := gA 1 1
    have hι₀S : ι₀ ∈ stdSylow ξ ψ :=
      gA_mem_stdSylow (Subgroup.one_mem _) (Subgroup.one_mem _)
    have hι₀V : ι₀ ∈ V := hle hι₀S
    have hg''V : (g * d⁻¹) * ι₀ ∈ V := Subgroup.mul_mem _ hg'V hι₀V
    have hg''eq : (g * d⁻¹) * ι₀ = gD w 1 := by
      rw [hw]
      dsimp only [ι₀]
      rw [gA_mul_gA, autU_one_aut, inv_one, mul_one, one_mul]
    obtain ⟨M, hM⟩ := hV2 ⟨(g * d⁻¹) * ι₀, hg''V⟩
    have hM' : ((g * d⁻¹) * ι₀) ^ 2 ^ M = 1 := by
      have := congrArg (fun x : ↥V => (x : PGammaL2 F)) hM
      simpa [Subgroup.coe_pow] using this
    rw [hg''eq] at hM'
    have hwM : w ^ 2 ^ M = 1 := by
      rw [gD_one_pow, ← gD_one_one] at hM'
      exact (gD_eq_iff.mp hM').1
    have hwmem : w ∈ Subgroup.zpowers ξ := mem_zpowers_of_two_power_order hξ hc1 hc2 hwM
    have hgdS : (g * d⁻¹) * ι₀ ∈ stdSylow ξ ψ := by
      rw [hg''eq]; exact gD_mem_stdSylow (Subgroup.one_mem _) hwmem
    have hg'dS : g * d⁻¹ ∈ stdSylow ξ ψ := by
      have h1 : ((g * d⁻¹) * ι₀) * ι₀⁻¹ ∈ stdSylow ξ ψ :=
        Subgroup.mul_mem _ hgdS (Subgroup.inv_mem _ hι₀S)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h1
    have h1 : (g * d⁻¹) * d ∈ stdSylow ξ ψ := Subgroup.mul_mem _ hg'dS hdmem
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h1

end Sylow

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
