module

public import CFSG.LargeExtraspecial.DW4Levi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W4

open Subgroup Module QuadraticMap
open scoped IsMulCommutative

variable {X : Type*} [Group X] [Finite X] {T : Setting X}

namespace Hyp

variable {W₁ W₂ : Submodule (ZMod 2) T.Qt} (H : Hyp T W₁ W₂)
include H

theorem fix_of_fix {e : T.Qt ≃ₗ[ZMod 2] T.Qt} (h1 : ∀ a ∈ W₁, e a ∈ W₁)
    (h2 : ∀ b ∈ W₂, e b ∈ W₂) {a b : T.Qt} (ha : a ∈ W₁) (hb : b ∈ W₂) (h : e (a + b) = a + b) :
    e a = a ∧ e b = b := by
  have hd : e a - a ∈ W₁ ⊓ W₂ := by
    refine ⟨W₁.sub_mem (h1 a ha) ha, ?_⟩
    have : e a - a = b - e b := by
      rw [map_add] at h
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]
    exact W₂.sub_mem hb (h2 b hb)
  rw [H.compl.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at hd
  refine ⟨hd, ?_⟩
  rw [map_add, hd] at h
  exact add_left_cancel h

theorem mul_self_eq_one_of_lift {U₀ U₀' : Subgroup X} (hU₀ : IsZCompl U₀ (T.clPre W₁) T.z)
    (hU₀' : IsZCompl U₀' (T.clPre W₂) T.z) {ℓ : X} (hℓM : ℓ ∈ T.M)
    (hℓ₁ : ℓ ∈ normalizer (U₀ : Set X)) (hℓ₂ : ℓ ∈ normalizer (U₀' : Set X)) {x : X}
    (hx : x * x = 1) (hxℓ : x * ℓ⁻¹ ∈ T.QG)
    (hfix : ∀ a ∈ W₁, ((T.ρ ⟨ℓ, hℓM⟩ : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) a = a →
      ∃ v ∈ W₁, a = ((T.ρ ⟨ℓ, hℓM⟩ : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v - v) :
    ℓ * ℓ = 1 := by
  set e := ((T.ρ ⟨ℓ, hℓM⟩ : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) with he
  set ν := x * ℓ⁻¹ with hν
  have hxν : x = ν * ℓ := by rw [hν, inv_mul_cancel_right]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hxM : x ∈ T.M := by
    rw [hxν]
    exact T.M.mul_mem (T.QG_le_M hxℓ) hℓM
  have hℓℓQ : ℓ * ℓ ∈ T.QG := by
    have e1 : ℓ * ℓ = ν⁻¹ * (x * ν⁻¹ * x⁻¹) := by
      rw [hxinv, hν]
      group
    rw [e1]
    exact T.QG.mul_mem (T.QG.inv_mem hxℓ) (T.conj_mem_QG hxM (T.QG.inv_mem hxℓ))
  have hℓℓ := H.eq_one_or_z_of_mem_normalizer hU₀ hU₀' hℓℓQ (mul_mem hℓ₁ hℓ₁)
    (mul_mem hℓ₂ hℓ₂)
  have hcl0 : T.cl (ℓ * ℓ)⁻¹ = 0 := by
    rw [T.cl_inv hℓℓQ]
    exact (T.cl_eq_zero_iff hℓℓQ).mpr hℓℓ
  have hfixν : e (T.cl ν) = T.cl ν := by
    have e2 : ℓ * ν * ℓ⁻¹ = ν⁻¹ * (ℓ * ℓ)⁻¹ := by
      have : ν * ℓ * (ν * ℓ) = 1 := by rw [← hxν]; exact hx
      calc ℓ * ν * ℓ⁻¹ = ν⁻¹ * (ν * ℓ * (ν * ℓ)) * (ℓ * ℓ)⁻¹ := by group
        _ = ν⁻¹ * (ℓ * ℓ)⁻¹ := by rw [this, mul_one]
    rw [he, T.ρ_cl ⟨ℓ, hℓM⟩ hxℓ]
    change T.cl (ℓ * ν * ℓ⁻¹) = T.cl ν
    rw [e2, T.cl_mul (T.QG.inv_mem hxℓ) (T.QG.inv_mem hℓℓQ), hcl0, add_zero, T.cl_inv hxℓ]
  obtain ⟨a, ha, b, hb, hab⟩ := H.exists_add_eq (T.cl ν)
  obtain ⟨hea, heb⟩ := H.fix_of_fix (fun a ha => H.inv₁ ⟨ℓ, hℓM⟩ a ha)
    (fun b hb => H.inv₂ ⟨ℓ, hℓM⟩ b hb) ha hb (by rw [hab]; exact hfixν)
  obtain ⟨u, hu, rfl⟩ := hU₀.exists_cl_eq ha
  obtain ⟨w, hw, rfl⟩ := hU₀'.exists_cl_eq hb
  have huQ := hU₀.mem_QG hu
  have hwQ := hU₀'.mem_QG hw
  have hℓu : ℓ * u * ℓ⁻¹ = u := hU₀.eq_of_cl_eq ((mem_normalizer_iff.mp hℓ₁ u).mp hu) hu (by
    rw [← T.ρ_cl ⟨ℓ, hℓM⟩ huQ]
    exact hea)
  have hℓw : ℓ * w * ℓ⁻¹ = w := hU₀'.eq_of_cl_eq ((mem_normalizer_iff.mp hℓ₂ w).mp hw) hw (by
    rw [← T.ρ_cl ⟨ℓ, hℓM⟩ hwQ]
    exact heb)
  have hpol : polar T.q (T.cl u) (T.cl w) = 0 := by
    obtain ⟨v, -, hvu⟩ := hfix _ (hU₀.cl_mem hu) hea
    have h3 : polar T.q (e v) (T.cl w) = polar T.q v (T.cl w) :=
      calc polar T.q (e v) (T.cl w) = polar T.q (e v) (e (T.cl w)) := by rw [heb]
        _ = polar T.q v (T.cl w) :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (T.ρ ⟨ℓ, hℓM⟩).2 v _
    rw [hvu, polar_sub_left, h3, sub_self]
  have huw : u * w = w * u := (T.polar_cl_eq_zero_iff huQ hwQ).mp hpol
  have hu2 : u * u = 1 := by
    have := (T.q_cl_eq_zero_iff huQ).mp (H.ts₁ _ (hU₀.cl_mem hu))
    rwa [pow_two] at this
  have hw2 : w * w = 1 := by
    have := (T.q_cl_eq_zero_iff hwQ).mp (H.ts₂ _ (hU₀'.cl_mem hw))
    rwa [pow_two] at this
  have huw2 : u * w * (u * w) = 1 :=
    calc u * w * (u * w) = u * (w * u) * w := by group
      _ = u * (u * w) * w := by rw [← huw]
      _ = u * u * (w * w) := by group
      _ = 1 := by rw [hu2, hw2, one_mul]
  have hνuw : ν = u * w ∨ ν = u * w * T.z :=
    (T.cl_eq_cl_iff (T.QG.mul_mem huQ hwQ) hxℓ).mp (by rw [T.cl_mul huQ hwQ, hab])
  have hzℓ : ℓ * T.z * ℓ⁻¹ = T.z := by rw [T.z_comm hℓM, mul_inv_cancel_right]
  have hzuw : T.z * (u * w) = u * w * T.z := (T.z_comm_QG (T.QG.mul_mem huQ hwQ)).symm
  have hℓν : ℓ * ν = ν * ℓ := by
    have h1 : ℓ * ν * ℓ⁻¹ = ν := by
      rcases hνuw with h | h <;> rw [h]
      · calc ℓ * (u * w) * ℓ⁻¹ = ℓ * u * ℓ⁻¹ * (ℓ * w * ℓ⁻¹) := by group
          _ = u * w := by rw [hℓu, hℓw]
      · calc ℓ * (u * w * T.z) * ℓ⁻¹ =
            ℓ * u * ℓ⁻¹ * (ℓ * w * ℓ⁻¹) * (ℓ * T.z * ℓ⁻¹) := by group
          _ = u * w * T.z := by rw [hℓu, hℓw, hzℓ]
    calc ℓ * ν = ℓ * ν * ℓ⁻¹ * ℓ := by group
      _ = ν * ℓ := by rw [h1]
  have hν2 : ν * ν = 1 := by
    rcases hνuw with h | h <;> rw [h]
    · exact huw2
    · calc u * w * T.z * (u * w * T.z) = u * w * (T.z * (u * w)) * T.z := by group
        _ = u * w * (u * w) * (T.z * T.z) := by rw [hzuw]; group
        _ = 1 := by rw [huw2, T.z_mul_z, one_mul]
  calc ℓ * ℓ = ν * ν * (ℓ * ℓ) := by rw [hν2, one_mul]
    _ = ν * ℓ * (ν * ℓ) := by
      rw [show ν * ℓ * (ν * ℓ) = ν * (ℓ * ν) * ℓ by group, hℓν]
      group
    _ = x * x := by rw [← hxν]
    _ = 1 := hx

end Hyp

end CFSG.LargeExtraspecial.DW.W4
