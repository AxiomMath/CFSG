module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y3S
public import CFSG.ClassicalInvolution.Q3.Q3WASNorm
public import CFSG.ClassicalInvolution.Q3.Q3WASTAsm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.Q3 (IsClassicalMember3)
open CFSG.Open (classicalInvolutionOddCore)

section Aux

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem locAut_inv_locAut (hΩ : ConjInvariant Ω) {t z : G} (ht : t * z * t⁻¹ = z)
    (ht' : t⁻¹ * z * t⁻¹⁻¹ = z) (a : locQuot Ω z) :
    Gaps.locAut hΩ ht' (Gaps.locAut hΩ ht a) = a := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ a
  show Gaps.locAut hΩ ht' (Gaps.locAut hΩ ht (Gaps.locMk Ω z y)) = Gaps.locMk Ω z y
  rw [Gaps.locAut_mk, Gaps.locAut_mk]
  congr 1
  apply Subtype.ext
  rw [Gaps.coe_layerAut, Gaps.coe_layerAut]
  group

end Aux

section Lift


theorem liftY {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}
    (c : Q3TP.TCtxS3 .PSU 4 Ω K z) : LiftYStmt c := by
  intro t ht K₂ K₂' T w hK₂ hK₂' hT hTQ hw hwt y₀ hy₀ h₂ h₂'
  classical
  have hwY : w ∈ locLayer Ω z := le_centralizingLayer hK₂ hw.mem
  have hΩ := c.hΩ.conjInvariant
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective _ y₀
  set y : G := (u : G) with hydef
  have hy : y ∈ locLayer Ω z := u.2
  have hyl : (⟨y, hy⟩ : ↥(locLayer Ω z)) = u := rfl
  have hyy₀ : Gaps.locMk Ω z ⟨y, hy⟩ = y₀ := by rw [hyl]; exact hu
  have hyz : y * z * y⁻¹ = z := by
    have := centralizingLayer_le_centralizer Ω {z} hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp this
    rw [mul_inv_eq_iff_eq_mul]
    exact h1
  have hlocy : ∀ a, Gaps.locAut hΩ hyz a = y₀ * a * y₀⁻¹ := fun a => by
    rw [locAut_eq_conj3 hΩ hy hyz a, hyy₀]
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := by
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 hyz c.hKz).mpr fun a ha => ?_
    rw [hlocy]
    have := c.d.comm₀ a (c.hQ₀ ha) y₀ hy₀
    rw [← this, mul_inv_cancel_right]
  have hTy : T ≤ Subgroup.centralizer ({y} : Set G) := by
    refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 hyz hT).mpr fun a ha => ?_
    rw [hlocy]
    have := c.d.comm₁ a (hTQ ha) y₀ hy₀
    rw [← this, mul_inv_cancel_right]
  have ht' : t⁻¹ * z * t⁻¹⁻¹ = z := by
    calc t⁻¹ * z * t⁻¹⁻¹ = t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ := by rw [ht]
      _ = z := by group
  have hu1 : (t⁻¹ * y) * z * (t⁻¹ * y)⁻¹ = z := by
    calc (t⁻¹ * y) * z * (t⁻¹ * y)⁻¹ = t⁻¹ * (y * z * y⁻¹) * t := by group
      _ = t⁻¹ * z * t := by rw [hyz]
      _ = t⁻¹ * (t * z * t⁻¹) * t := by rw [ht]
      _ = z := by group
  have hact : ∀ {M : Subgroup G}, M ∈ centralizingMembers Ω {z} →
      (∀ a ∈ locImg Ω z M, y₀ * a * y₀⁻¹ = Gaps.locAut hΩ ht a) →
      ∀ k ∈ M, y * k * y⁻¹ = t * k * t⁻¹ := by
    intro M hM hMa k hk
    have hfix : M ≤ Subgroup.centralizer ({t⁻¹ * y} : Set G) := by
      refine (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 hu1 hM).mpr fun a ha => ?_
      rw [locAut_mul3 hΩ ht' hyz hu1, hlocy, hMa a ha, locAut_inv_locAut hΩ ht ht']
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hfix hk)
    calc y * k * y⁻¹ = t * (t⁻¹ * y * k) * y⁻¹ := by group
      _ = t * (k * (t⁻¹ * y)) * y⁻¹ := by rw [h1]
      _ = t * k * t⁻¹ := by group
  have hcomm : y₀ * Gaps.locMk Ω z ⟨w, hwY⟩ = Gaps.locMk Ω z ⟨w, hwY⟩ * y₀ := by
    have hmem : Gaps.locMk Ω z ⟨w, hwY⟩ ∈ locImg Ω z K₂ :=
      ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr hw.mem, rfl⟩
    have h1 := h₂ _ hmem
    have h2 : Gaps.locAut hΩ ht (Gaps.locMk Ω z ⟨w, hwY⟩) = Gaps.locMk Ω z ⟨w, hwY⟩ := by
      rw [Gaps.locAut_mk]
      congr 1
      apply Subtype.ext
      rw [Gaps.coe_layerAut]
      calc t * w * t⁻¹ = w * t * t⁻¹ := by rw [hwt]
        _ = w := by group
    rw [h2] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hwsq : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw.orderOf_eq_two, pow_two] at this
  have hyw : y * w * y⁻¹ = w := by
    set Y : ↥(locLayer Ω z) := ⟨y, hy⟩ with hY
    set W : ↥(locLayer Ω z) := ⟨w, hwY⟩ with hW
    set O := classicalInvolutionOddCore ↥(locLayer Ω z) with hO
    have hOc : O ≤ Subgroup.center ↥(locLayer Ω z) := c.hP1
    have hmem : W⁻¹ * (Y * W * Y⁻¹) ∈ O := by
      have h1 : Gaps.locMk Ω z (W⁻¹ * (Y * W * Y⁻¹)) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hyy₀, hcomm, mul_inv_cancel_right,
          inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    set e : ↥(locLayer Ω z) := W⁻¹ * (Y * W * Y⁻¹) with he
    have hWsq : W * W = 1 := Subtype.ext hwsq
    have hec : ∀ g : ↥(locLayer Ω z), g * e = e * g := fun g =>
      (Subgroup.mem_center_iff.mp (hOc hmem) g)
    have hYW : Y * W * Y⁻¹ = W * e := by rw [he]; group
    have he2 : e * e = 1 := by
      have h1 : (Y * W * Y⁻¹) * (Y * W * Y⁻¹) = 1 := by
        calc (Y * W * Y⁻¹) * (Y * W * Y⁻¹) = Y * (W * W) * Y⁻¹ := by group
          _ = 1 := by rw [hWsq]; group
      rw [hYW] at h1
      calc e * e = (W * W) * (e * e) := by rw [hWsq, one_mul]
        _ = W * (W * e) * e := by group
        _ = W * (e * W) * e := by rw [hec W]
        _ = (W * e) * (W * e) := by group
        _ = 1 := h1
    have he1 : e = 1 := by
      have hdvd : orderOf (⟨e, hmem⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      have hdvd2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact he2)
      have hodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card _
      rw [Subgroup.orderOf_mk] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hdvd
        exact absurd (even_iff_two_dvd.mpr hdvd) (Nat.not_even_iff_odd.mpr hodd)
    rw [he1, mul_one] at hYW
    have := congrArg Subtype.val hYW
    simpa using this
  exact ⟨y, hy, hyy₀, hyw, hKy, hTy, hact hK₂ h₂, hact hK₂' h₂'⟩

end Lift

end CFSG.ClassicalInvolution.Q3.Q3P21
