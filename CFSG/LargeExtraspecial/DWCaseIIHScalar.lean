module

public import CFSG.LargeExtraspecial.DWCaseIIHAlt

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting CFSG.ClassicalGroups.Alternating
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ω : BilinForm (ZMod 2) V}

theorem exists_eq_smul_one_add_sw (hω : ω.IsAlt) (hnd : ω.Nondegenerate)
    (h4 : 4 ≤ finrank (ZMod 2) V) {v : V} (hv : v ≠ 0) {D : Module.End (ZMod 2) V}
    (hD : IsAltEnd ω D) (hP : ∀ u, ω u v = 0 → D u ∈ span (ZMod 2) {u, v}) :
    ∃ (α : ZMod 2) (e : V), D = α • 1 + sw ω v e := by
  obtain ⟨⟨b, hvb⟩, hsplit⟩ := alternating_hyperbolic_splitting hω hnd hv
  obtain ⟨-, -, hmemW, -, hndW, hdimW⟩ := hsplit b hvb
  set W := ω.orthogonal (span (ZMod 2) {v, b}) with hW
  have hbv : ω b v = 1 := by rw [bilin_comm_of_isAlt hω, hvb]
  have hWv : ∀ w ∈ W, ω w v = 0 := fun w hw => (hmemW w).mp hw v (subset_span (by simp))
  have hWb : ∀ w ∈ W, ω w b = 0 := fun w hw => (hmemW w).mp hw b (subset_span (by simp))
  have hspan_v : ∀ x ∈ W, ∀ y ∈ span (ZMod 2) {v}, ω x y = 0 := by
    intro x hx y hy
    obtain ⟨c, rfl⟩ := mem_span_singleton.mp hy
    rw [map_smul, hWv x hx, smul_zero]
  have hl : ∀ w ∈ W, ∃ l : ZMod 2, D w + l • w ∈ span (ZMod 2) {v} := by
    intro w hw
    obtain ⟨a, c, hac⟩ := mem_span_pair.mp (hP w (hWv w hw))
    refine ⟨a, mem_span_singleton.mpr ⟨c, ?_⟩⟩
    rw [← hac]
    zmod_two_module
  have heq : ∀ w ∈ W, ∀ x ∈ W, ω x w = 1 → ∀ l l' : ZMod 2, D w + l • w ∈ span (ZMod 2) {v} →
      D x + l' • x ∈ span (ZMod 2) {v} → l = l' := by
    intro w hw x hx hxw l l' h h'
    have hwx : ω w x = 1 := by rw [bilin_comm_of_isAlt hω, hxw]
    have h1 := hspan_v x hx _ h
    have h2 := hspan_v w hw _ h'
    rw [map_add, map_smul, hxw, smul_eq_mul, mul_one] at h1
    rw [map_add, map_smul, hwx, smul_eq_mul, mul_one, ← hD.symm] at h2
    exact (zmod_two_eq_of_add_eq_zero h1).symm.trans (zmod_two_eq_of_add_eq_zero h2)
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdimW
    omega
  obtain ⟨w₀, hw₀, hw₀0⟩ := exists_mem_ne_zero_of_ne_bot hWne
  obtain ⟨α, hα₀⟩ := hl w₀ hw₀
  have hα : ∀ w ∈ W, D w + α • w ∈ span (ZMod 2) {v} := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0, map_zero, smul_zero, add_zero]
      exact zero_mem _
    obtain ⟨y, hy₀, hy⟩ := alternating_common_nonorthogonal_vector (isAlt_restrict hω W) hndW
      (u := ⟨w₀, hw₀⟩) (v := ⟨w, hw⟩) (fun h => hw₀0 (congrArg Subtype.val h))
      (fun h => hw0 (congrArg Subtype.val h))
    have hy₀' : ω y w₀ = 1 := by
      rw [bilin_comm_of_isAlt hω]
      exact zmod_two_eq_one_of_ne_zero hy₀
    have hy' : ω w y = 1 := zmod_two_eq_one_of_ne_zero hy
    obtain ⟨ly, hly⟩ := hl y y.2
    obtain ⟨lw, hlw⟩ := hl w hw
    have e1 := heq w₀ hw₀ y y.2 hy₀' α ly hα₀ hly
    have e2 := heq y y.2 w hw hy' ly lw hly hlw
    rwa [e1, e2]
  obtain ⟨c, hc⟩ : ∃ c : ZMod 2, D v = c • v := by
    have h := hP v (hω.self_eq_zero v)
    rw [Set.pair_eq_singleton] at h
    obtain ⟨c, hc⟩ := mem_span_singleton.mp h
    exact ⟨c, hc.symm⟩
  refine ⟨α, D b + α • b, ?_⟩
  set e := D b + α • b with he
  set F : Module.End (ZMod 2) V := D + α • 1 + sw ω v e with hF
  have hFapp : ∀ y, F y = D y + α • y + sw ω v e y := fun y => rfl
  have hFv : F v = 0 := by
    have hve : ω v e = c + α := by
      rw [he, map_add, map_smul, hvb, smul_eq_mul, mul_one, hD.symm, hc, map_smul, hbv,
        smul_eq_mul, mul_one]
    rw [hFapp, sw_apply, hω.self_eq_zero v, zero_smul, add_zero, hve, hc]
    zmod_two_module
  have hFb : F b = 0 := by
    have hbe : ω b e = 0 := by
      rw [he, map_add, map_smul, hD b, hω.self_eq_zero b, smul_zero, add_zero]
    rw [hFapp, sw_apply, hbe, zero_smul, zero_add, hbv, one_smul, he]
    zmod_two_module
  have hFW : ∀ w ∈ W, F w = 0 := by
    intro w hw
    obtain ⟨c', hc'⟩ := mem_span_singleton.mp (hα w hw)
    have hDw : D w = c' • v + α • w := by rw [hc']; zmod_two_module
    have hwe : ω w e = c' := by
      have hbw : ω b w = 0 := by rw [bilin_comm_of_isAlt hω, hWb w hw]
      rw [he, map_add, map_smul, hWb w hw, smul_zero, add_zero, hD.symm, hDw, map_add,
        map_smul, map_smul, hbv, hbw, smul_eq_mul, smul_eq_mul, mul_one, mul_zero, add_zero]
    rw [hFapp, sw_apply, hwe, hWv w hw, zero_smul, add_zero, hDw]
    zmod_two_module
  have hπ : ∀ y, y + ω y b • v + ω y v • b ∈ W := by
    intro y
    refine (hmemW _).mpr fun h hh => ?_
    obtain ⟨s, t, rfl⟩ := mem_span_pair.mp hh
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hω.self_eq_zero,
      hvb, hbv, smul_eq_mul, mul_zero, mul_one, add_zero]
    rw [ZModModule.add_self, CharTwo.add_self_eq_zero, mul_zero, mul_zero, add_zero]
  ext y
  have hy : F y = 0 := by
    have h1 : y = (y + ω y b • v + ω y v • b) + ω y b • v + ω y v • b := by zmod_two_module
    rw [h1, map_add, map_add, map_smul, map_smul, hFW _ (hπ y), hFv, hFb, smul_zero, smul_zero,
      add_zero, add_zero]
  rw [hFapp] at hy
  rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  exact (vec_eq_of_add_eq_zero (by rw [← add_assoc]; exact hy))

end CFSG.LargeExtraspecial.DW
