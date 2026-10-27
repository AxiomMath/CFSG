module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitL34PField

public section

namespace CFSG.ComponentClassification.TBLit.L34P

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_mem_oddIn_of_pow {K : Subgroup X} {g : X} (hg : g ∈ K) {k : ℕ}
    (hk : g ^ (2 ^ k) = 1) (h : jq K ⟨g, hg⟩ = 1) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (zpowers g) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hk, one_zpow]
  exact eq_one_of_jq_eq_one (zpowers_le.mpr hg) hP (mem_zpowers g) h

theorem exists_rho
    {α β γ : X}
    {K L : Subgroup X} (hK : ⁅K, K⁆ = K) (hL34 : IsL34Type (K ⧸ Open.fusionZStar K))
    (hβN : β ∈ normalizer (K : Set X)) (hβ2 : β * β = 1) (hLK : L ≤ K)
    (hLβ : L ≤ centralizer ({β} : Set X)) {F : Type*} [Field F] [Finite F]
    (h7 : Nat.card F = 7) (e : ↥L ⧸ pPrimeCore 2 ↥L ≃* SL(2, F))
    (hfield : HarrisLit.EndB.IsL34Field K β) (hunit : IsL34Unitary K α)
    (hγ : orderOf γ = 2) (hγK : γ ∈ K) (hKγ : K ≤ centralizer ({γ} : Set X))
    (hβγ : β * γ = γ * β) :
    ∃ ρ ∈ K, ρ * β = β * ρ ∧ ρ ∈ zStarIn K ∧ ρ * ρ = γ ∧ α⁻¹ * ρ * α * ρ ∈ oddIn K := by
  obtain ⟨q, l, hQS, -, hzz, hinj⟩ := exists_field_frame hK hL34 hβN hβ2 hLK hLβ h7 e hfield
  set gh : Jhat K := jq K ⟨γ, hγK⟩ with hgh
  have hγc : gh ∈ center (Jhat K) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := jq_surjective K g
    rw [hgh, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKγ k.2))
  obtain ⟨a, b, hab⟩ := (mem_ker_iff hQS.ql hQS.lsurj hQS.three).1 (hQS.ker ▸ hγc)
  rw [← zz_ofNat] at hab
  have hfixγ : betaHat K hβN gh = gh := by
    rw [hgh, betaHat_mk]
    congr 1
    refine Subtype.ext ?_
    show β⁻¹ * γ * β = γ
    rw [mul_assoc, ← hβγ, ← mul_assoc, inv_mul_cancel, one_mul]
  have hb : (b : ZMod 4) = 0 := by
    have h1 : zz l (3 * (b : ZMod 4)) (2 * (b : ZMod 4)) = 1 := by
      have h2 := hfixγ
      rw [hab, hzz] at h2
      calc zz l (3 * (b : ZMod 4)) (2 * (b : ZMod 4)) =
          zz l ((a : ZMod 4) + 3 * (b : ZMod 4)) (3 * (b : ZMod 4)) *
            (zz l (a : ZMod 4) (b : ZMod 4))⁻¹ := by
            rw [zz_inv, zz_mul]
            congr 1 <;> ring
        _ = 1 := by rw [h2, mul_inv_cancel]
    have h3 := (hinj _ _ h1).1
    have key : ∀ d : ZMod 4, 3 * d = 0 → d = 0 := by decide
    exact key _ h3
  rw [hb] at hab
  have hγ2 : γ * γ = 1 := by rw [← pow_two, ← hγ, pow_orderOf_eq_one]
  have ha : (a : ZMod 4) = 2 := by
    have h1 : zz l (2 * (a : ZMod 4)) 0 = 1 := by
      have h2 : gh * gh = 1 := by
        rw [hgh, ← map_mul]
        have : (⟨γ, hγK⟩ : K) * ⟨γ, hγK⟩ = 1 := Subtype.ext hγ2
        rw [this, map_one]
      rw [hab, zz_mul] at h2
      rw [← h2]
      congr 1
      ring
    have h2 := (hinj _ _ h1).1
    have hne : (a : ZMod 4) ≠ 0 := by
      intro h0
      rw [h0] at hab
      have h3 : jq K ⟨γ, hγK⟩ = 1 := by rw [← hgh, hab, zz_zero]
      have h4 := eq_one_of_mem_oddIn_of_pow hγK (k := 1) (by rw [pow_one, pow_two, hγ2]) h3
      rw [h4, orderOf_one] at hγ
      exact absurd hγ (by norm_num)
    have key : ∀ c : ZMod 4, 2 * c = 0 → c ≠ 0 → c = 2 := by decide
    exact key _ h2 hne
  rw [ha] at hab
  have hfixρ : betaHat K hβN (zz l 1 0) = zz l 1 0 := by
    rw [hzz, mul_zero, add_zero]
  obtain ⟨j, hj, hjβ⟩ := exists_fixed_lift hβN hβ2 hfixρ
  have hjβ' : (j : X) * β = β * j := by
    have h1 : β⁻¹ * (j : X) * β = j := by
      have := congrArg Subtype.val hjβ
      rwa [coe_conjJ] at this
    calc (j : X) * β = β * (β⁻¹ * (j : X) * β) := by group
      _ = β * j := by rw [h1]
  have hord : orderOf (j : X) ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hord
  set ρ : X := (j : X) ^ m with hρ
  have hρK : ρ ∈ K := K.pow_mem j.2 m
  have hρ2k : ρ ^ (2 ^ k) = 1 := by
    rw [hρ, ← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hjqρ : jq K ⟨ρ, hρK⟩ = zz l (m : ZMod 4) 0 := by
    have h1 : (⟨ρ, hρK⟩ : K) = j ^ m := Subtype.ext (SubgroupClass.coe_pow j m).symm
    rw [h1, map_pow, hj, zz_pow, mul_one, mul_zero]
  have hm2 : (m : ZMod 4) + (m : ZMod 4) = 2 := by
    obtain ⟨t, rfl⟩ := hm
    push_cast
    have key : ∀ u : ZMod 4, (2 * u + 1) + (2 * u + 1) = 2 := by decide
    exact key _
  refine ⟨ρ, hρK, ?_, ?_, ?_, ?_⟩
  · rw [hρ]
    exact (Commute.pow_left hjβ' m).eq
  · rw [mem_zStarIn_iff hρK, hjqρ, ← hQS.ker]
    exact zz_mem_ker hQS _ _
  · have hγρ : (ρ * ρ) * γ⁻¹ = 1 := by
      have hg : (ρ * ρ) * γ⁻¹ ∈ K := K.mul_mem (K.mul_mem hρK hρK) (K.inv_mem hγK)
      have hcomm : Commute ρ γ := mem_centralizer_singleton_iff.mp (hKγ hρK)
      refine eq_one_of_mem_oddIn_of_pow hg (k := k + 1) ?_ ?_
      · have hcomm' : Commute (ρ * ρ) γ⁻¹ := (hcomm.mul_left hcomm).inv_right
        have h1 : (ρ * ρ) ^ (2 ^ (k + 1)) = 1 := by
          rw [← pow_two, ← pow_mul, pow_succ, show 2 * (2 ^ k * 2) = 2 ^ k * 4 by ring,
            pow_mul, hρ2k, one_pow]
        have h2 : γ⁻¹ ^ (2 ^ (k + 1)) = 1 := by
          rw [inv_pow, pow_succ', pow_mul, pow_two, hγ2, one_pow, inv_one]
        rw [hcomm'.mul_pow, h1, h2, one_mul]
      · have e1 : (⟨(ρ * ρ) * γ⁻¹, hg⟩ : K) = ⟨ρ, hρK⟩ * ⟨ρ, hρK⟩ * (⟨γ, hγK⟩)⁻¹ := rfl
        rw [e1, map_mul, map_mul, map_inv, hjqρ, ← hgh, hab, zz_mul, hm2, add_zero,
          mul_inv_cancel]
    calc ρ * ρ = (ρ * ρ) * γ⁻¹ * γ := by group
      _ = γ := by rw [hγρ, one_mul]
  · obtain ⟨qU, hqUS, hqUsurj, hqUker, h3U, hαU⟩ := exists_unitary_realization hK hL34 hunit
    obtain ⟨lU, hlU, hlUs⟩ :=
      exists_lam (commutator_jhat hK) qU hqUS hqUsurj (hqUker ▸ le_refl _)
    have hU : IsUSetting qU lU (betaHat K hunit.1) := ⟨hqUS, hqUsurj, hqUker, h3U, hlU, hlUs, hαU⟩
    have hc : jq K ⟨ρ, hρK⟩ ∈ qU.ker := by
      rw [hqUker, hjqρ, ← hQS.ker]
      exact zz_mem_ker hQS _ _
    have hinv := hU.beta_ker hc
    rw [betaHat_mk] at hinv
    have hmem : α⁻¹ * ρ * α ∈ K := conj_mem_of_mem_normalizer hunit.1 hρK
    rw [mem_oddIn_iff (K.mul_mem hmem hρK)]
    have e1 : (⟨α⁻¹ * ρ * α * ρ, K.mul_mem hmem hρK⟩ : K) = ⟨α⁻¹ * ρ * α, hmem⟩ * ⟨ρ, hρK⟩ := rfl
    rw [e1, map_mul, hinv, inv_mul_cancel]

end CFSG.ComponentClassification.TBLit.L34P
