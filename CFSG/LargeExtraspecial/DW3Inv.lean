module

public import CFSG.LargeExtraspecial.DW3Data
public import CFSG.LargeExtraspecial.DWTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W3

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.DW.W4
open scoped IsMulCommutative

variable {X : Type*} [Group X] [Finite X] {T : Setting X}

namespace Hyp

variable {W₁ W₂ : Submodule (ZMod 2) T.Qt} (H : Hyp T W₁ W₂)
include H

theorem conj_eq_of_fix {U₀ U₀' : Subgroup X} (hU₀ : IsZCompl U₀ (T.clPre W₁) T.z)
    (hU₀' : IsZCompl U₀' (T.clPre W₂) T.z) {ℓ : X} (hℓM : ℓ ∈ T.M)
    (hℓ₁ : ℓ ∈ normalizer (U₀ : Set X)) (hℓ₂ : ℓ ∈ normalizer (U₀' : Set X)) {c : X}
    (hc : c ∈ T.QG)
    (hfix : ((T.ρ ⟨ℓ, hℓM⟩ : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) (T.cl c) = T.cl c) :
    ℓ * c * ℓ⁻¹ = c := by
  obtain ⟨a, ha, b, hb, hab⟩ := H.exists_add_eq (T.cl c)
  obtain ⟨hea, heb⟩ := H.fix_of_fix (fun a ha => H.inv₁ ⟨ℓ, hℓM⟩ a ha)
    (fun b hb => H.inv₂ ⟨ℓ, hℓM⟩ b hb) ha hb (by rw [hab]; exact hfix)
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
  have hzℓ : ℓ * T.z * ℓ⁻¹ = T.z := by rw [T.z_comm hℓM, mul_inv_cancel_right]
  rcases (T.cl_eq_cl_iff (T.QG.mul_mem huQ hwQ) hc).mp (by rw [T.cl_mul huQ hwQ, hab]) with
    rfl | rfl
  · calc ℓ * (u * w) * ℓ⁻¹ = ℓ * u * ℓ⁻¹ * (ℓ * w * ℓ⁻¹) := by group
      _ = u * w := by rw [hℓu, hℓw]
  · calc ℓ * (u * w * T.z) * ℓ⁻¹ = ℓ * u * ℓ⁻¹ * (ℓ * w * ℓ⁻¹) * (ℓ * T.z * ℓ⁻¹) := by group
      _ = u * w * T.z := by rw [hℓu, hℓw, hzℓ]

theorem mul_self_eq_one_of_maxEA {U₀ U₀' : Subgroup X} (hU₀ : IsZCompl U₀ (T.clPre W₁) T.z)
    (hU₀' : IsZCompl U₀' (T.clPre W₂) T.z) {ℓ : X} (hℓM : ℓ ∈ T.M)
    (hℓ₁ : ℓ ∈ normalizer (U₀ : Set X)) (hℓ₂ : ℓ ∈ normalizer (U₀' : Set X)) {x : X}
    (hx : x * x = 1) (hxℓ : x * ℓ⁻¹ ∈ T.QG) {A : Subgroup X} [IsElementaryAbelian 2 A]
    (hA : MaxEA T A) (hAx : ∀ a ∈ A, x * a = a * x) : ℓ * ℓ = 1 := by
  set e := ((T.ρ ⟨ℓ, hℓM⟩ : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) with he
  set ν := x * ℓ⁻¹ with hν
  have hxν : x = ν * ℓ := by rw [hν, inv_mul_cancel_right]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hνM : ν ∈ T.M := T.QG_le_M hxℓ
  have hxM : x ∈ T.M := by
    rw [hxν]
    exact T.M.mul_mem hνM hℓM
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
  have e2 : ℓ * ν * ℓ⁻¹ = ν⁻¹ * (ℓ * ℓ)⁻¹ := by
    have : ν * ℓ * (ν * ℓ) = 1 := by rw [← hxν]; exact hx
    calc ℓ * ν * ℓ⁻¹ = ν⁻¹ * (ν * ℓ * (ν * ℓ)) * (ℓ * ℓ)⁻¹ := by group
      _ = ν⁻¹ * (ℓ * ℓ)⁻¹ := by rw [this, mul_one]
  have hfixν : e (T.cl ν) = T.cl ν := by
    rw [he, T.ρ_cl ⟨ℓ, hℓM⟩ hxℓ]
    change T.cl (ℓ * ν * ℓ⁻¹) = T.cl ν
    rw [e2, T.cl_mul (T.QG.inv_mem hxℓ) (T.QG.inv_mem hℓℓQ), hcl0, add_zero, T.cl_inv hxℓ]
  have hℓν : ℓ * ν * ℓ⁻¹ = ν := H.conj_eq_of_fix hU₀ hU₀' hℓM hℓ₁ hℓ₂ hxℓ hfixν
  have hνν : (ℓ * ℓ)⁻¹ = ν * ν := by
    calc (ℓ * ℓ)⁻¹ = ν * (ν⁻¹ * (ℓ * ℓ)⁻¹) := by group
      _ = ν * ν := by rw [← e2, hℓν]
  have hρx : T.ρ ⟨x, hxM⟩ = T.ρ ⟨ℓ, hℓM⟩ := by
    have h1 : (⟨x, hxM⟩ : T.M) = ⟨ν, hνM⟩ * ⟨ℓ, hℓM⟩ := Subtype.ext hxν
    rw [h1, map_mul, (T.ρ_eq_one_iff ⟨ν, hνM⟩).mpr hxℓ, one_mul]
  have hνA : ∀ a ∈ A, a * ν = ν * a := by
    intro a ha
    have haQ := hA.le_QG ha
    have hxa : x * a * x⁻¹ = a := by rw [hAx a ha, mul_inv_cancel_right]
    have hea : e (T.cl a) = T.cl a := by
      rw [he, ← hρx, T.ρ_cl ⟨x, hxM⟩ haQ]
      change T.cl (x * a * x⁻¹) = T.cl a
      rw [hxa]
    have hℓa := H.conj_eq_of_fix hU₀ hU₀' hℓM hℓ₁ hℓ₂ haQ hea
    have h1 : ν * a * ν⁻¹ = a := by
      calc ν * a * ν⁻¹ = ν * (ℓ * a * ℓ⁻¹) * ν⁻¹ := by rw [hℓa]
        _ = (ν * ℓ) * a * (ν * ℓ)⁻¹ := by group
        _ = a := by rw [← hxν, hxa]
    calc a * ν = ν * a * ν⁻¹ * ν := by rw [h1]
      _ = ν * a := by group
  have hνmem : ν ∈ A := by
    rw [← hA.QG_inf_centralizer]
    exact ⟨hxℓ, mem_centralizer_iff.mpr hνA⟩
  have hν2 : ν * ν = 1 := MaxEA.mul_self_of_mem hνmem
  calc ℓ * ℓ = ((ℓ * ℓ)⁻¹)⁻¹ := (inv_inv _).symm
    _ = 1 := by rw [hνν, hν2, inv_one]

end Hyp

end CFSG.LargeExtraspecial.DW.W3
