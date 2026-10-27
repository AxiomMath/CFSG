module

public import CFSG.LargeExtraspecial.DWTransSL
public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}

namespace MaxEA

variable [IsElementaryAbelian 2 A] (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)) {h : G}
  (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A)
include hA hM hxQ hxA

omit [IsElementaryAbelian 2 A] hM hxQ hxA in
theorem Ubar_le_Lbar : Ubar S A h ≤ S.Lbar h := by
  apply Subgroup.map_mono
  intro m hm
  rw [mem_subgroupOf] at hm ⊢
  exact ⟨(hA.conj h).le_QG hm.1, hm.2⟩

theorem mem_Ubar_of_resAt_mem {y : S.O} (hy : y ∈ S.Mbar)
    (hfix : resAt S A hM ⟨y, hy⟩ ∈ fixer (axisForm S A (h * S.z * h⁻¹))) : y ∈ Ubar S A h := by
  obtain ⟨u, hu, hut⟩ := hA.exists_Ubar_resAt_eq hM hxQ hxA hfix
  have hyu : y = u := (congrArg Subtype.val (hA.resAt_injective hM hut)).symm
  rw [hyu]
  exact hu

theorem Lbar_eq_Ubar : S.Lbar h = Ubar S A h := by
  refine le_antisymm (fun ℓ hℓ => ?_) (hA.Ubar_le_Lbar)
  have hℓM : ℓ ∈ S.Mbar := S.Lbar_le_Mbar h hℓ
  have := S.isElementaryAbelian_Lbar hxQ
  set φ := axisForm S A (h * S.z * h⁻¹)
  have hcomm : ∀ c (hc : φ c = 0), resAt S A hM ⟨ℓ, hℓM⟩ * LinearEquiv.transvection hc =
      LinearEquiv.transvection hc * resAt S A hM ⟨ℓ, hℓM⟩ := by
    intro c hc
    obtain ⟨u, hu, hut⟩ := hA.exists_Ubar_resAt_eq hM hxQ hxA (g := LinearEquiv.transvection hc)
      fun w hw => by rw [transvection_apply, hw, zero_smul, add_zero]
    rw [← hut, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show ℓ * u = u * ℓ
    exact congrArg Subtype.val (mul_comm (⟨ℓ, hℓ⟩ : S.Lbar h) ⟨u, hA.Ubar_le_Lbar hu⟩)
  exact hA.mem_Ubar_of_resAt_mem hM hxQ hxA hℓM fun w hw =>
    fix_of_commute_transvections (hA.axisForm_ne_zero hxQ hxA) _ hcomm hw

omit hM in
theorem one_le_width : 1 ≤ S.width := by
  by_contra h0
  have h0' : S.width = 0 := by omega
  have hcl := hA.cl_conj_ne_zero hxQ hxA
  have h2 : finrank (ZMod 2) S.Qt = 0 := by rw [S.finrank_Qt_eq_two_mul_width, h0']
  have : Finite (Additive S.Q) := inferInstanceAs (Finite S.Q)
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hsub : Subsingleton S.Qt := Module.finrank_zero_iff.mp h2
  exact hcl (Subsingleton.elim _ _)

theorem card_QG_inf_Qa : Nat.card (S.QG ⊓ S.Qa h : Subgroup G) = 2 ^ (S.width + 1) := by
  have h1 := S.card_Lbar_mul h
  rw [hA.Lbar_eq_Ubar hM hxQ hxA, hA.card_Ubar hM hxQ hxA,
    S.card_L0 hxQ (hA.conj_ne_z hxA)] at h1
  have hw := hA.one_le_width hxQ hxA
  have e : 2 ^ (2 * S.width) = 2 ^ (S.width - 1) * 2 ^ (S.width + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e] at h1
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h1

omit [Finite G] [IsElementaryAbelian 2 A] hA hM hxQ hxA in
theorem linearEquiv_inv_apply {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (f : E ≃ₗ[ZMod 2] E) (x : E) : (f⁻¹ : E ≃ₗ[ZMod 2] E) x = f.symm x :=
  rfl

theorem fix_of_resAt_mem_ker (hn : 3 ≤ S.width) {y : S.O} (hy : y ∈ S.Mbar)
    (hker : ∀ w, axisForm S A (h * S.z * h⁻¹) w = 0 →
      axisForm S A (h * S.z * h⁻¹) (resAt S A hM ⟨y, hy⟩ w) = 0) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹) := by
  have := finite_clSub (S := S) (A := A)
  obtain ⟨m, rfl⟩ := hy
  rw [← S.timmesfeld_12_4_1 hxQ (hA.conj_ne_z hxA) hn m, hA.Lbar_eq_Ubar hM hxQ hxA]
  have hker' : ∀ w, axisForm S A (h * S.z * h⁻¹) w = 0 →
      axisForm S A (h * S.z * h⁻¹) ((resAt S A hM ⟨S.ρ m, ⟨m, rfl⟩⟩).symm w) = 0 := by
    let f : LinearMap.ker (axisForm S A (h * S.z * h⁻¹)) →
        LinearMap.ker (axisForm S A (h * S.z * h⁻¹)) :=
      fun w => ⟨resAt S A hM ⟨S.ρ m, ⟨m, rfl⟩⟩ w, hker w w.2⟩
    have hf : Function.Injective f := fun a b hab =>
      Subtype.ext ((resAt S A hM ⟨S.ρ m, ⟨m, rfl⟩⟩).injective (congrArg Subtype.val hab))
    intro w hw
    obtain ⟨w', hw'⟩ := (Finite.injective_iff_surjective.mp hf) ⟨w, hw⟩
    have e : resAt S A hM ⟨S.ρ m, ⟨m, rfl⟩⟩ w' = w := congrArg Subtype.val hw'
    rw [← e, LinearEquiv.symm_apply_apply]
    exact w'.2
  rw [mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    have hmem : S.ρ m * u * (S.ρ m)⁻¹ ∈ S.Mbar :=
      S.Mbar.mul_mem (S.Mbar.mul_mem ⟨m, rfl⟩ (Ubar_le_Mbar h hu)) (S.Mbar.inv_mem ⟨m, rfl⟩)
    refine hA.mem_Ubar_of_resAt_mem hM hxQ hxA hmem fun w hw => ?_
    have e1 : (⟨S.ρ m * u * (S.ρ m)⁻¹, hmem⟩ : S.Mbar) =
        ⟨S.ρ m, ⟨m, rfl⟩⟩ * ⟨u, Ubar_le_Mbar h hu⟩ * (⟨S.ρ m, ⟨m, rfl⟩⟩ : S.Mbar)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      linearEquiv_inv_apply, hA.resAt_Ubar_fix hM hxQ hxA hu _ (hker' w hw),
      LinearEquiv.apply_symm_apply]
  · intro hu
    have huM : u ∈ S.Mbar := by
      have := S.Mbar.mul_mem (S.Mbar.mul_mem (S.Mbar.inv_mem ⟨m, rfl⟩) (Ubar_le_Mbar h hu))
        (⟨m, rfl⟩ : S.ρ m ∈ S.Mbar)
      rwa [show (S.ρ m)⁻¹ * (S.ρ m * u * (S.ρ m)⁻¹) * S.ρ m = u by group] at this
    refine hA.mem_Ubar_of_resAt_mem hM hxQ hxA huM fun w hw => ?_
    have e1 : (⟨u, huM⟩ : S.Mbar) = (⟨S.ρ m, ⟨m, rfl⟩⟩ : S.Mbar)⁻¹ *
        ⟨S.ρ m * u * (S.ρ m)⁻¹, Ubar_le_Mbar h hu⟩ * ⟨S.ρ m, ⟨m, rfl⟩⟩ := by
      apply Subtype.ext
      change u = (S.ρ m)⁻¹ * (S.ρ m * u * (S.ρ m)⁻¹) * S.ρ m
      group
    rw [e1, map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      linearEquiv_inv_apply, hA.resAt_Ubar_fix hM hxQ hxA hu _ (hker w hw),
      LinearEquiv.symm_apply_apply]

omit hM in
theorem apply_mem_clSub_inf_of_fix {y : S.O} (hy : y ∈ S.Mbar)
    (hfix : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹)) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa h)) :
    (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa h) := by
  obtain ⟨m, rfl⟩ := hy
  have hne := hA.conj_ne_z hxA
  rw [S.ρ_cl m hxQ] at hfix
  have hmxQ := S.conj_mem_QG m.2 hxQ
  obtain ⟨m', hm'M, hρ, hm'x⟩ : ∃ m' : G, ∃ hm' : m' ∈ S.M, S.ρ ⟨m', hm'⟩ = S.ρ m ∧
      m' * (h * S.z * h⁻¹) * m'⁻¹ = h * S.z * h⁻¹ := by
    rcases (S.cl_eq_cl_iff hxQ hmxQ).mp hfix.symm with e | e
    · exact ⟨m, m.2, rfl, e⟩
    · have hx1 : h * S.z * h⁻¹ ≠ 1 := fun e1 => (hA.cl_conj_ne_zero hxQ hxA)
        (by rw [e1, S.cl_one])
      obtain ⟨q, hq, hqx⟩ := S.exists_conj_eq_mul_z hxQ hx1 hne
      refine ⟨q * m, S.M.mul_mem (S.QG_le_M hq) m.2, ?_, ?_⟩
      · have e2 : (⟨q * m, S.M.mul_mem (S.QG_le_M hq) m.2⟩ : S.M) = ⟨q, S.QG_le_M hq⟩ * m := rfl
        rw [e2, map_mul, (S.ρ_eq_one_iff _).mpr hq, one_mul]
      · rw [show q * (m : G) * (h * S.z * h⁻¹) * (q * m)⁻¹ =
            q * ((m : G) * (h * S.z * h⁻¹) * (m : G)⁻¹) * q⁻¹ by group, e,
          show q * (h * S.z * h⁻¹ * S.z) * q⁻¹ = q * (h * S.z * h⁻¹) * q⁻¹ * (q * S.z * q⁻¹) by
            group, hqx, show q * S.z * q⁻¹ = S.z by rw [S.z_comm (S.QG_le_M hq),
            mul_inv_cancel_right], mul_assoc, S.z_mul_z, mul_one]
  obtain ⟨b, hb, hbQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [← hρ, S.ρ_cl ⟨m', hm'M⟩ hbQ]
  have hm'T : m' ∈ (S.conjBy h).M := by
    rw [(S.conjBy h).mem_M_iff, Setting.conjBy_z]
    calc m' * (h * S.z * h⁻¹) = m' * (h * S.z * h⁻¹) * m'⁻¹ * m' := by group
      _ = (h * S.z * h⁻¹) * m' := by rw [hm'x]
  exact S.cl_mem_clSub ⟨S.conj_mem_QG hm'M hb.1, (S.conjBy h).conj_mem_QG hm'T hb.2⟩
    (S.conj_mem_QG hm'M hb.1)

end MaxEA

end CFSG.LargeExtraspecial.DW
