module

public import CFSG.LargeExtraspecial.A2ModBasicThird

import CFSG.LargeExtraspecial.A2ModHub
import CFSG.LargeExtraspecial.AS35QCoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.LargeExtraspecial.A2Mod

open Module CFSG.RankThree.OrthogonalInvolutions

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem RootClass.exists_conj (hD : RootClass X D) {d e : X} (hd : d ∈ D) (he : e ∈ D) :
    ∃ x : X, x * d * x⁻¹ = e := by
  obtain ⟨d₀, -, hcl⟩ := hD.1.2.1
  rw [hcl] at hd he
  exact isConj_iff.mp (hd.symm.trans he)

theorem RootClass.exists_partner (hD : RootClass X D) {r : X} (hr : r ∈ D) :
    ∃ e ∈ D, e ≠ r ∧ r * e = e * r ∧ r * e ∈ D := by
  obtain ⟨α, hα, β, hβ, h4⟩ := hD.2.1
  have hζ : (α * β) ^ 2 ∈ D := hD.1.2.2.2.2 α hα β hβ h4
  have hα2 : α * α = 1 := hD.mul_self hα
  have hβ2 : β * β = 1 := hD.mul_self hβ
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have hβi : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ2
  have hord4 : (α * β) ^ 4 = 1 := by
    rw [← h4]
    exact pow_orderOf_eq_one _
  have hζζ : (α * β) ^ 2 * (α * β) ^ 2 = 1 := by
    rw [← pow_add]
    exact hord4
  have hζne : (α * β) ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at this
    exact absurd this (by norm_num)
  have hβαβ : β * α * β⁻¹ ∈ D := hD.conj_mem β α hα
  have hprod : α * (β * α * β⁻¹) = (α * β) ^ 2 := by
    rw [hβi, pow_two]
    group
  have hcomm : α * (β * α * β⁻¹) = (β * α * β⁻¹) * α := by
    rw [hprod]
    have h1 : (β * α * β⁻¹) * α = ((α * β) ^ 2)⁻¹ := by
      rw [hβi, pow_two, mul_inv_rev, mul_inv_rev, hαi, hβi]
      group
    rw [h1]
    exact (inv_eq_of_mul_eq_one_right hζζ).symm
  have hne : β * α * β⁻¹ ≠ α := by
    intro h1
    apply hζne
    rw [← hprod, h1, hα2]
  obtain ⟨x, hx⟩ := hD.exists_conj hα hr
  refine ⟨x * (β * α * β⁻¹) * x⁻¹, hD.conj_mem x _ hβαβ, ?_, ?_, ?_⟩
  · intro h1
    apply hne
    have h2 : x * (β * α * β⁻¹) * x⁻¹ = x * α * x⁻¹ := h1.trans hx.symm
    have h3 := mul_left_cancel (mul_right_cancel h2)
    exact h3
  · rw [← hx]
    calc x * α * x⁻¹ * (x * (β * α * β⁻¹) * x⁻¹)
        = x * (α * (β * α * β⁻¹)) * x⁻¹ := by group
      _ = x * ((β * α * β⁻¹) * α) * x⁻¹ := by rw [hcomm]
      _ = x * (β * α * β⁻¹) * x⁻¹ * (x * α * x⁻¹) := by group
  · rw [← hx]
    have h1 : x * α * x⁻¹ * (x * (β * α * β⁻¹) * x⁻¹) = x * (α * β) ^ 2 * x⁻¹ := by
      calc x * α * x⁻¹ * (x * (β * α * β⁻¹) * x⁻¹)
          = x * (α * (β * α * β⁻¹)) * x⁻¹ := by group
        _ = x * (α * β) ^ 2 * x⁻¹ := by rw [hprod]
    rw [h1]
    exact hD.conj_mem x _ hζ

theorem RootClass.false_of_transitive [Finite X] (hD : RootClass X D) (hA : A2Action D Q ρ)
    {r : X} (hr : r ∈ D) {v : V} (hv0 : v ≠ 0) (_hvr : v ∈ commSpace (ρ r))
    (htrans : ∀ u ∈ commSpace (ρ r), u ≠ 0 → ∃ c : X, c * r = r * c ∧ ρ c v = u)
    (hT2 : {d : X | ∃ g : X, ρ g v = v ∧ d = g * r * g⁻¹}.ncard ≤ 2) : False := by
  obtain ⟨e, he, hne, -, hre⟩ := hD.exists_partner hr
  obtain ⟨-, hfin, hle, -⟩ := hA.third_line hr he hre
  have hbot : commSpace (ρ r) ⊓ commSpace (ρ e) ≠ ⊥ := Submodule.one_le_finrank_iff.mp hfin.ge
  obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).mp hbot
  have hpr : p ∈ commSpace (ρ r) := (Submodule.mem_inf.mp hp).1
  have hpe : p ∈ commSpace (ρ e) := (Submodule.mem_inf.mp hp).2
  have hpre : p ∈ commSpace (ρ (r * e)) := hle hp
  obtain ⟨c, hcr, hcv⟩ := htrans p hpr hp0
  set O : Set X := {d : X | ∃ g : X, ρ g v = v ∧ d = g * r * g⁻¹} with hO
  have hsub : {d : X | d ∈ D ∧ p ∈ commSpace (ρ d)} ⊆ (fun d => c * d * c⁻¹) '' O := by
    rintro d ⟨hdD, hpd⟩
    have hd' : c⁻¹ * d * c ∈ D := by
      have := hD.conj_mem c⁻¹ d hdD
      rwa [inv_inv] at this
    have hvc : v = (ρ c)⁻¹ p := by
      rw [← hcv]
      simp [LinearEquiv.mul_apply]
    have hvd' : v ∈ commSpace (ρ (c⁻¹ * d * c)) := by
      have h1 : ρ (c⁻¹ * d * c) = ρ c⁻¹ * ρ d * (ρ c⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_inv, inv_inv]
      rw [h1, CFSG.LargeExtraspecial.AS35QCo.commSpace_conj, Submodule.mem_map]
      refine ⟨p, hpd, ?_⟩
      rw [hvc, map_inv]
      rfl
    obtain ⟨y, hy⟩ := hD.exists_conj hr hd'
    have hvy : v ∈ (commSpace (ρ r)).map (ρ y : V →ₗ[ZMod 2] V) := by
      have h1 : ρ (c⁻¹ * d * c) = ρ y * ρ r * (ρ y)⁻¹ := by
        rw [← hy, map_mul, map_mul, map_inv]
      rw [h1, CFSG.LargeExtraspecial.AS35QCo.commSpace_conj] at hvd'
      exact hvd'
    obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hvy
    have hu0 : u ≠ 0 := by
      rintro rfl
      apply hv0
      rw [← huv]
      simp
    obtain ⟨c', hc'r, hc'u⟩ := htrans u hu hu0
    refine ⟨c⁻¹ * d * c, ⟨y * c', ?_, ?_⟩, ?_⟩
    · rw [map_mul, LinearEquiv.mul_apply, hc'u]
      exact huv
    · rw [← hy]
      have hcc : c' * r * c'⁻¹ = r := by
        rw [hc'r]
        group
      calc y * r * y⁻¹ = y * (c' * r * c'⁻¹) * y⁻¹ := by rw [hcc]
        _ = y * c' * r * (y * c')⁻¹ := by group
    · group
  have h3 : ({r, e, r * e} : Set X).ncard = 3 := by
    refine Set.ncard_eq_three.mpr ⟨r, e, r * e, hne.symm, ?_, ?_, rfl⟩
    · intro h1
      have : e = 1 := by
        have h2 : r * 1 = r * e := by rw [mul_one]; exact h1
        exact (mul_left_cancel h2).symm
      exact hD.ne_one he this
    · intro h1
      have : r = 1 := by
        have h2 : 1 * e = r * e := by rw [one_mul]; exact h1
        exact (mul_right_cancel h2).symm
      exact hD.ne_one hr this
  have hsub3 : ({r, e, r * e} : Set X) ⊆ {d : X | d ∈ D ∧ p ∈ commSpace (ρ d)} := by
    intro d hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨hr, hpr⟩
    · exact ⟨he, hpe⟩
    · exact ⟨hre, hpre⟩
  have h4 : 3 ≤ ((fun d => c * d * c⁻¹) '' O).ncard := by
    rw [← h3]
    exact Set.ncard_le_ncard (hsub3.trans hsub) (Set.toFinite _)
  have h5 : ((fun d => c * d * c⁻¹) '' O).ncard ≤ O.ncard := Set.ncard_image_le (Set.toFinite _)
  omega

theorem A2Action.fix_of_isPGroup_three [Finite X] (hA : A2Action D Q ρ) {r : X} (hr : r ∈ D)
    {v : V} (hv0 : v ≠ 0) (hvr : v ∈ commSpace (ρ r))
    (hn : ¬ ∀ u ∈ commSpace (ρ r), u ≠ 0 → ∃ c : X, c * r = r * c ∧ ρ c v = u)
    (T : Subgroup X) (hT : IsPGroup 3 ↥T) (hTr : ∀ t ∈ T, t * r = r * t) :
    ∀ t ∈ T, ρ t v = v := by
  classical
  obtain ⟨-, -, -, hdim, -⟩ := hA.2.2.2 r hr
  push Not at hn
  obtain ⟨u₀, hu₀P, hu₀0, hu₀⟩ := hn
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  letI : MulAction ↥T V := MulAction.compHom V (ρ.comp T.subtype)
  have hsmul : ∀ t : ↥T, t • v = ρ (t : X) v := fun t => rfl
  have hPcard : ((commSpace (ρ r) : Submodule (ZMod 2) V) : Set V).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    have := CFSG.LargeExtraspecial.AS35QCo.natCard_submodule (commSpace (ρ r))
    rw [hdim] at this
    simpa using this
  have hsub : MulAction.orbit ↥T v ⊆
      ((commSpace (ρ r) : Submodule (ZMod 2) V) : Set V) \ {0, u₀} := by
    rintro x ⟨t, ht⟩
    have hx : x = ρ (t : X) v := ht.symm.trans (hsmul t)
    have htr := hTr t t.2
    refine ⟨?_, ?_⟩
    · rw [hx]
      obtain ⟨u, rfl⟩ := mem_commSpace.mp hvr
      refine mem_commSpace.mpr ⟨ρ (t : X) u, ?_⟩
      have hc : ρ r (ρ (t : X) u) = ρ (t : X) (ρ r u) := by
        rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, htr]
      rw [map_sub, hc]
    · rintro (h0 | h0)
      · apply hv0
        rw [hx] at h0
        have : ρ (t : X) v = ρ (t : X) 0 := by rw [h0, map_zero]
        exact (ρ (t : X)).injective this
      · exact hu₀ (t : X) htr (by rw [← hx]; exact h0)
  have hsub2 : ({0, u₀} : Set V) ⊆ ((commSpace (ρ r) : Submodule (ZMod 2) V) : Set V) := by
    intro x hx
    rcases hx with rfl | rfl
    · exact Submodule.zero_mem _
    · exact hu₀P
  have h2 : (((commSpace (ρ r) : Submodule (ZMod 2) V) : Set V) \ {0, u₀}).ncard = 2 := by
    rw [Set.ncard_diff hsub2 (Set.toFinite _), hPcard, Set.ncard_pair (Ne.symm hu₀0)]
  have hle : (MulAction.orbit ↥T v).ncard ≤ 2 := by
    rw [← h2]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  obtain ⟨n, hn3⟩ := hT.card_orbit v
  rw [Nat.card_coe_set_eq] at hn3
  have hn0 : n = 0 := by
    by_contra hne
    have : 3 ^ 1 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hne)
    omega
  rw [hn0, pow_zero] at hn3
  intro t ht
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hn3
  have h1 : v ∈ MulAction.orbit ↥T v := MulAction.mem_orbit_self v
  have h2 : (⟨t, ht⟩ : ↥T) • v ∈ MulAction.orbit ↥T v := MulAction.mem_orbit _ _
  rw [hx] at h1 h2
  rw [Set.mem_singleton_iff] at h1 h2
  have := h2.trans h1.symm
  rwa [hsmul] at this

end CFSG.LargeExtraspecial.A2Mod
