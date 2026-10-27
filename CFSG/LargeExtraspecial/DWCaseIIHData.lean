module

public import CFSG.LargeExtraspecial.DWCaseIIHLines

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.GroupTheory.GLnTwoSplitting CFSG.ClassicalGroups.Alternating
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure TvData (ω : BilinForm (ZMod 2) V) (D : V → Module.End (ZMod 2) V) (α : V → ZMod 2)
    (e : V → V) : Prop where
  e_zero : e 0 = 0
  eq : ∀ v, v ≠ 0 → D v = α v • 1 + sw ω v (e v)
  symm : ∀ u v, ω u v = 0 → ω u (e v) = ω v (e u)
  rel3 : ∀ u v, ω u v = 1 → ∀ x, D (u + v) x =
    D u x + tv ω u (D v (tv ω u x) + tv ω v (D u (tv ω v (tv ω u x))))

variable {ω : BilinForm (ZMod 2) V} {D : V → Module.End (ZMod 2) V} {α : V → ZMod 2} {e : V → V}

theorem ne_zero_of_apply_eq_one (hω : ω.IsAlt) {u v : V} (huv : ω u v = 1) :
    u ≠ 0 ∧ v ≠ 0 ∧ u + v ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, map_zero, LinearMap.zero_apply] at huv
    exact zero_ne_one huv
  · rw [h, map_zero] at huv
    exact zero_ne_one huv
  · rw [vec_eq_of_add_eq_zero h, hω.self_eq_zero] at huv
    exact zero_ne_one huv

namespace TvData

variable (hd : TvData ω D α e) (hω : ω.IsAlt)
include hd hω

theorem smul_one_eq {u v : V} (huv : ω u v = 1) :
    (α (u + v) + α v) • (1 : Module.End (ZMod 2) V) = sw ω u (e u) +
      sw ω (u + v) (tv ω u (e v)) + sw ω v (tv ω u (tv ω v (e u))) + sw ω (u + v) (e (u + v)) := by
  obtain ⟨hu0, hv0, huv0⟩ := ne_zero_of_apply_eq_one hω huv
  have htuv : tv ω u v = u + v := by
    rw [tv_apply, bilin_comm_of_isAlt hω, huv, one_smul, add_comm]
  have htvu : tv ω v u = u + v := by rw [tv_apply, huv, one_smul]
  have htu : tv ω u (u + v) = v := by
    rw [tv_apply, map_add, LinearMap.add_apply, hω.self_eq_zero, zero_add,
      bilin_comm_of_isAlt hω, huv, one_smul]
    abel_two
  ext x
  have key := hd.rel3 u v huv x
  rw [hd.eq (u + v) huv0, hd.eq u hu0, hd.eq v hv0] at key
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
    tv_tv ω hω, apply_sw_apply (tv_isometry hω u) (tv_tv ω hω u),
    apply_sw_apply (tv_isometry hω v) (tv_tv ω hω v), htuv, htvu, htu] at key
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  linear_combination (norm := zmod_two_module) key

theorem alpha_add_eq (h6 : 6 ≤ finrank (ZMod 2) V) {u v : V} (huv : ω u v = 1) :
    α (u + v) = α v := by
  by_contra hne
  have h1 : α (u + v) + α v = 1 := by
    rcases zmod_two_eq_zero_or_one (α (u + v) + α v) with h | h
    · exact absurd (zmod_two_eq_of_add_eq_zero h) hne
    · exact h
  have key := hd.smul_one_eq hω huv
  rw [h1, one_smul] at key
  set S := span (ZMod 2) (Set.range ![u, v, e u, e v, e (u + v)]) with hS
  have hmem : ∀ i, ![u, v, e u, e v, e (u + v)] i ∈ S := fun i =>
    subset_span (Set.mem_range_self i)
  have hu : u ∈ S := hmem 0
  have hv : v ∈ S := hmem 1
  have heu : e u ∈ S := hmem 2
  have hev : e v ∈ S := hmem 3
  have heuv : e (u + v) ∈ S := hmem 4
  have htv : ∀ a ∈ S, ∀ y ∈ S, tv ω a y ∈ S := fun a ha y hy => add_mem hy (smul_mem _ _ ha)
  have hsw : ∀ a ∈ S, ∀ b ∈ S, ∀ x, sw ω a b x ∈ S := fun a ha b hb x =>
    add_mem (smul_mem _ _ ha) (smul_mem _ _ hb)
  have htop : ∀ x : V, x ∈ S := by
    intro x
    have hx := LinearMap.congr_fun key x
    rw [Module.End.one_apply] at hx
    rw [hx]
    simp only [LinearMap.add_apply]
    exact add_mem (add_mem (add_mem (hsw _ hu _ heu x)
      (hsw _ (add_mem hu hv) _ (htv _ hu _ hev) x))
      (hsw _ hv _ (htv _ hu _ (htv _ hv _ heu)) x)) (hsw _ (add_mem hu hv) _ heuv x)
  have h2 : S = ⊤ := eq_top_iff.mpr fun x _ => htop x
  have h3 := finrank_range_le_card (R := ZMod 2) ![u, v, e u, e v, e (u + v)]
  rw [Set.finrank, ← hS, h2, finrank_top, Fintype.card_fin] at h3
  omega

theorem alpha_eq_of_apply_eq_one (h6 : 6 ≤ finrank (ZMod 2) V) {u v : V} (huv : ω u v = 1) :
    α u = α v := by
  have hvu : ω v u = 1 := by rw [bilin_comm_of_isAlt hω, huv]
  have h1 := hd.alpha_add_eq hω h6 huv
  have h2 := hd.alpha_add_eq hω h6 hvu
  rw [add_comm] at h2
  rw [← h2, h1]

variable [FiniteDimensional (ZMod 2) V]

theorem alpha_eq (hnd : ω.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) {u v : V} (hu : u ≠ 0)
    (hv : v ≠ 0) : α u = α v := by
  obtain ⟨w, huw, hvw⟩ := alternating_common_nonorthogonal_vector hω hnd hu hv
  rw [hd.alpha_eq_of_apply_eq_one hω h6 (zmod_two_eq_one_of_ne_zero huw),
    hd.alpha_eq_of_apply_eq_one hω h6 (zmod_two_eq_one_of_ne_zero hvw)]

theorem add_add_mem_span (hnd : ω.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) {u v : V}
    (huv : ω u v = 1) : e u + e v + e (u + v) + (ω (e v) u + ω (e u) u + ω (e u) v) • u ∈
      span (ZMod 2) {u + v} := by
  obtain ⟨-, -, huv0⟩ := ne_zero_of_apply_eq_one hω huv
  have hvu : ω v u = 1 := by rw [bilin_comm_of_isAlt hω, huv]
  have key := hd.smul_one_eq hω huv
  rw [hd.alpha_add_eq hω h6 huv, CharTwo.add_self_eq_zero, zero_smul] at key
  refine mem_span_of_sw_eq_zero hω hnd huv0 ?_
  rw [key]
  ext x
  simp only [sw_apply, tv_apply, map_add, map_smul, LinearMap.add_apply, smul_eq_mul, hvu]
  zmod_two_module

theorem q_add_eq (hnd : ω.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) {u v : V}
    (huv : ω u v = 1) : ω (u + v) (e (u + v)) = ω v (e v) := by
  have hvu : ω v u = 1 := by rw [bilin_comm_of_isAlt hω, huv]
  obtain ⟨c, hc⟩ := mem_span_singleton.mp (hd.add_add_mem_span hω hnd h6 huv)
  have h1 : e (u + v) = c • (u + v) + e u + e v + (ω (e v) u + ω (e u) u + ω (e u) v) • u := by
    rw [hc]
    zmod_two_module
  rw [h1]
  simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul, hω.self_eq_zero, huv, hvu,
    bilin_comm_of_isAlt hω (e v) u, bilin_comm_of_isAlt hω (e u) u, bilin_comm_of_isAlt hω (e u) v]
  ring_nf
  reduce_mod_char

theorem q_eq_of_apply_eq_one (hnd : ω.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) {u v : V}
    (huv : ω u v = 1) : ω u (e u) = ω v (e v) := by
  have hvu : ω v u = 1 := by rw [bilin_comm_of_isAlt hω, huv]
  have h1 := hd.q_add_eq hω hnd h6 huv
  have h2 := hd.q_add_eq hω hnd h6 hvu
  rw [add_comm] at h2
  rw [← h2, h1]

omit [FiniteDimensional (ZMod 2) V] in
theorem q_add_of_apply_eq_zero {x y : V} (hxy : ω x y = 0) :
    ω (x + y) (e (x + y)) = ω x (e x) + ω y (e y) := by
  have hyx : ω y x = 0 := by rw [bilin_comm_of_isAlt hω, hxy]
  have hx : ω x (x + y) = 0 := by rw [map_add, hω.self_eq_zero, hxy, add_zero]
  have hy : ω y (x + y) = 0 := by rw [map_add, hω.self_eq_zero, hyx, zero_add]
  rw [map_add, LinearMap.add_apply, hd.symm x _ hx, hd.symm y _ hy]
  simp only [map_add, LinearMap.add_apply, hd.symm x y hxy]
  ring_nf
  reduce_mod_char

theorem q_eq_zero (hnd : ω.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) (v : V) :
    ω v (e v) = 0 := by
  by_cases hv : v = 0
  · rw [hv, hd.e_zero, map_zero]
  have hQ : ∀ u, u ≠ 0 → ω u (e u) = ω v (e v) := by
    intro u hu
    obtain ⟨w, huw, hvw⟩ := alternating_common_nonorthogonal_vector hω hnd hu hv
    rw [hd.q_eq_of_apply_eq_one hω hnd h6 (zmod_two_eq_one_of_ne_zero huw),
      hd.q_eq_of_apply_eq_one hω hnd h6 (zmod_two_eq_one_of_ne_zero hvw)]
  have hlt : finrank (ZMod 2) (span (ZMod 2) {v}) <
      finrank (ZMod 2) (ω.orthogonal (span (ZMod 2) {v})) := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd]
    have := finrank_span_singleton (K := ZMod 2) hv
    omega
  obtain ⟨y, hy, hyv⟩ := exists_mem_notMem_of_finrank_lt hlt
  have hvy : ω v y = 0 := LinearMap.BilinForm.mem_orthogonal_iff.mp hy v (mem_span_singleton_self v)
  have hy0 : y ≠ 0 := fun h => hyv (h ▸ zero_mem _)
  have hvy0 : v + y ≠ 0 := fun h => hyv (by
    rw [← vec_eq_of_add_eq_zero h]
    exact mem_span_singleton_self v)
  have h1 := hd.q_add_of_apply_eq_zero hω hvy
  rw [hQ _ hvy0, hQ _ hy0] at h1
  have h2 : ω v (e v) + ω v (e v) = 0 := CharTwo.add_self_eq_zero _
  rw [← h1] at h2
  exact h2

theorem add_mem_span (hnd : ω.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) (u v : V) :
    e (u + v) + e u + e v ∈ span (ZMod 2) {u, v} := by
  by_cases huv : ω u v = 0
  · by_contra hn
    obtain ⟨x, hx, hx1⟩ := exists_apply_eq_one_of_notMem hω hnd hn
    have hxu : ω x u = 0 := hx u (subset_span (by simp))
    have hxv : ω x v = 0 := hx v (subset_span (by simp))
    have hxuv : ω x (u + v) = 0 := by rw [map_add, hxu, hxv, add_zero]
    rw [map_add, map_add, hd.symm x (u + v) hxuv, hd.symm x u hxu, hd.symm x v hxv, map_add,
      LinearMap.add_apply] at hx1
    have h2 : ω u (e x) + ω v (e x) + ω u (e x) + ω v (e x) = 0 := by
      ring_nf
      reduce_mod_char
    rw [hx1] at h2
    exact one_ne_zero h2
  · have huv1 : ω u v = 1 := zmod_two_eq_one_of_ne_zero huv
    obtain ⟨c, hc⟩ := mem_span_singleton.mp (hd.add_add_mem_span hω hnd h6 huv1)
    have h1 : e (u + v) + e u + e v =
        c • (u + v) + (ω (e v) u + ω (e u) u + ω (e u) v) • u := by
      rw [hc]
      zmod_two_module
    rw [h1]
    refine add_mem (smul_mem _ _ (add_mem (subset_span (by simp)) (subset_span (by simp))))
      (smul_mem _ _ (subset_span (by simp)))

theorem exists_isAltEnd (hnd : ω.Nondegenerate) (h6 : 6 ≤ finrank (ZMod 2) V) :
    ∃ (a : ZMod 2) (w : Module.End (ZMod 2) V), IsAltEnd ω w ∧
      ∀ v, v ≠ 0 → D v = a • 1 + sw ω v (w v) := by
  obtain ⟨w, hw⟩ := exists_linearMap_add_mem_span e hd.e_zero (hd.add_mem_span hω hnd h6)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hwv : ∀ v, ∃ c : ZMod 2, w v = c • v + e v := fun v => by
    obtain ⟨c, hc⟩ := mem_span_singleton.mp (hw v)
    exact ⟨c, by rw [hc]; abel_two⟩
  refine ⟨α v₀, w, fun v => ?_, fun v hv => ?_⟩
  · obtain ⟨c, hc⟩ := hwv v
    rw [hc, map_add, map_smul, hω.self_eq_zero, smul_zero, zero_add, hd.q_eq_zero hω hnd h6 v]
  · obtain ⟨c, hc⟩ := hwv v
    rw [hd.eq v hv, hd.alpha_eq hω hnd h6 hv hv₀, hc, sw_add_right, sw_smul_right, sw_self,
      smul_zero, zero_add]

end TvData

end CFSG.LargeExtraspecial.DW
