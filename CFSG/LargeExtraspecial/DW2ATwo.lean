module

public import CFSG.LargeExtraspecial.DW2ABasic
public import CFSG.LargeExtraspecial.DWTransFaith
public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

theorem cl_eq_zero_of_mem_Qa_of_mem_perp (hW : IsMbarInvariant S W) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hx : S.cl (g * S.z * g⁻¹) ∉ perp S W) {y : G} (hy : y ∈ S.QG ⊓ S.Qa g)
    (hyW : S.cl y ∈ perp S W) : S.cl y = 0 := by
  by_contra h0
  by_cases hyx : S.cl y = S.cl (g * S.z * g⁻¹)
  · exact hx (hyx ▸ hyW)
  obtain ⟨-, t, ht, hty⟩ := S.conj_L0_of_mem_QG_inf_Qa haQ hne hy ⟨h0, hyx⟩
  have htM := S.L0_le_M g ht
  have h1 : S.cl (t * y * t⁻¹) ∈ perp S W := by
    rw [← S.ρ_cl ⟨t, htM⟩ hy.1]
    exact hW.perp ⟨t, htM⟩ _ hyW
  rw [hty, S.cl_mul haQ hy.1] at h1
  apply hx
  have := (perp S W).sub_mem h1 hyW
  rwa [add_sub_cancel_right] at this

theorem Lbar_fix_of_mem_perp (hW : IsMbarInvariant S W) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hx : S.cl (g * S.z * g⁻¹) ∉ perp S W) {t : S.O}
    (ht : t ∈ S.Lbar g) {v : S.Qt} (hv : v ∈ perp S W)
    (hva : polar S.q (S.cl (g * S.z * g⁻¹)) v = 0) : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨y, hy, -, hyv⟩ := S.mem_clSub_iff.mp (S.s12_Lbar_apply_sub_mem haQ ht hva)
  obtain ⟨m, hm⟩ := S.Lbar_le_Mbar g ht
  have htv : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ perp S W := by
    rw [← hm]
    exact hW.perp m v hv
  have hyW : S.cl y ∈ perp S W := by
    rw [hyv]
    exact sub_mem htv hv
  have h0 := cl_eq_zero_of_mem_Qa_of_mem_perp hW haQ hne hx hy hyW
  rw [hyv] at h0
  exact sub_eq_zero.mp h0

theorem cl_conj_mem_perp (hW : IsMbarInvariant S W) (hWW : W ≤ perp S W)
    (hlt : finrank (ZMod 2) W < S.width) {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) :
    S.cl (g * S.z * g⁻¹) ∈ perp S W := by
  by_cases hne : g * S.z * g⁻¹ = S.z
  · rw [hne, S.cl_z]
    exact zero_mem _
  by_contra hx
  set a := S.cl (g * S.z * g⁻¹) with ha
  obtain ⟨w₀, hw₀, hw₀a⟩ : ∃ w₀ ∈ W, polar S.q a w₀ ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    rw [mem_perp]
    intro w hw
    rw [polar_comm]
    exact h w hw
  have hw₀a' : polar S.q a w₀ = 1 := (zmod2_cases _).resolve_left hw₀a
  have hfix : ∀ t ∈ S.Lbar g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ = w₀ → t = 1 := by
    intro t ht htw
    have hall : ∀ v ∈ perp S W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      intro v hv
      by_cases hva : polar S.q a v = 0
      · exact Lbar_fix_of_mem_perp hW hxQ hne hx ht hv hva
      · have hva' : polar S.q a v = 1 := (zmod2_cases _).resolve_left hva
        have hsum : polar S.q a (v + w₀) = 0 := by
          rw [polar_add_right, hva', hw₀a']
          rfl
        have h1 := Lbar_fix_of_mem_perp hW hxQ hne hx ht (add_mem hv (hWW hw₀)) hsum
        rw [map_add, htw] at h1
        exact add_right_cancel h1
    obtain ⟨m, hm⟩ := S.Lbar_le_Mbar g ht
    have hy : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ Ybar S := ⟨t, ⟨m, hm⟩, rfl⟩
    exact Subtype.ext (eq_one_of_trivial_perp hW hy (fun w hw => hall w (hWW hw))
      fun v hv => by rw [hall v hv, sub_self]; exact zero_mem _)
  set K : Submodule (ZMod 2) S.Qt := W ⊓ perp S (ZMod 2 ∙ a)
  have hmemK : ∀ t : S.Lbar g, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ - w₀ ∈ K := by
    intro t
    obtain ⟨m, hm⟩ := S.Lbar_le_Mbar g t.2
    refine Submodule.mem_inf.mpr ⟨sub_mem (by rw [← hm]; exact hW m w₀ hw₀) hw₀, ?_⟩
    rw [mem_perp]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hta := S.s12_Lbar_apply_cl_a hxQ t.2
    rw [← ha] at hta
    have key : polar S.q a (((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀) = polar S.q a w₀ := by
      calc polar S.q a (((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀)
          = polar S.q (((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) a)
              (((t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀) := by rw [hta]
        _ = polar S.q a w₀ := polar_apply_apply (t : S.O) a w₀
    rw [polar_smul_left, polar_sub_right, key, sub_self, smul_zero]
  have hinj : Function.Injective (fun t : S.Lbar g =>
      (⟨(t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ - w₀, hmemK t⟩ : K)) := by
    intro t t' htt
    have e : (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ = (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ := by
      have := congrArg Subtype.val htt
      simpa using this
    have h1 : ((t'⁻¹ * t : S.Lbar g) : S.O) = 1 := by
      refine hfix _ (t'⁻¹ * t).2 ?_
      have h3 : (((t'⁻¹ * t : S.Lbar g) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀ =
          ((t' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) w₀) := rfl
      rw [h3, e]
      exact LinearEquiv.symm_apply_apply _ _
    have h2 : t'⁻¹ * t = 1 := Subtype.ext h1
    exact (inv_mul_eq_one.mp h2).symm
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [S.card_submodule] at hcard
  have hge := S.card_Lbar_ge hxQ hne
  have hKlt : finrank (ZMod 2) K < finrank (ZMod 2) W := by
    refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => ?_)
    have : w₀ ∈ K := h ▸ hw₀
    apply hw₀a
    have h3 := mem_perp.mp this.2 a (Submodule.mem_span_singleton_self a)
    exact h3
  have h4 : 2 ^ (S.width - 1) ≤ 2 ^ finrank (ZMod 2) K := hge.trans hcard
  have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  omega

end CFSG.LargeExtraspecial.DW
