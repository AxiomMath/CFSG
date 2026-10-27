module

public import CFSG.CGT.Harada80.OrthoFacts

public section

namespace CFSG.CGT.HaradaParrott80

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LargeExtraspecial.OrthoF2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem polar_sub_eq_zero {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {v : V} (hgv : g v = v) (y : V) : polar Q (g y - y) v = 0 := by
  rw [polar_sub_left, ← polar_map_of_mem hg y v, hgv, sub_self]

theorem apply_eq_of_sub_mem_span {v : V} (hv : Q v = 0) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {y : V} (hy : polar Q y v ≠ 0)
    (h : g y - y ∈ (ZMod 2) ∙ v) : g y = y := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have hgy : g y = y + c • v := by rw [hc]; abel
  have hQ := map_of_mem hg y
  rw [hgy, QuadraticMap.map_add Q, map_smul_zmod2 Q c v, hv, mul_zero, add_zero,
    polar_smul_right_eq Q c y v] at hQ
  have hc0 : c = 0 := (mul_eq_zero.mp (add_eq_left.mp hQ)).resolve_right hy
  rw [hgy, hc0, zero_smul, add_zero]

variable [FiniteDimensional (ZMod 2) V]

theorem sub_not_mem_span_of_mem_rootGroup (hQ : (polarBilin Q).Nondegenerate) {v : V}
    (hv : Q v = 0) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ rootGroup Q v) (hg1 : g ≠ 1) {y : V}
    (hy : polar Q y v ≠ 0) : g y - y ∉ (ZMod 2) ∙ v := by
  intro h
  by_cases hv0 : v = 0
  · subst hv0
    obtain ⟨w, -, rfl⟩ := mem_rootGroup.mp hg
    exact hg1 (eichler_zero_left Q w)
  obtain ⟨hgO, hgv, hgperp⟩ := (mem_rootGroup_iff hQ hv hv0).mp hg
  have hroot : CFSG.CGT.Harada80.IsRootElt Q v g := by
    refine ⟨hgO, hgv, fun z hz => ?_⟩
    obtain ⟨c, hc⟩ := hgperp z hz
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  exact hg1 (CFSG.CGT.Harada80.IsRootElt.eq_one_of_apply_eq hQ hv hroot hy
    (apply_eq_of_sub_mem_span hv hgO hy h))

theorem exists_mem_rootGroup_ne_one (hQ : (polarBilin Q).Nondegenerate) {v : V} (hv : Q v = 0)
    (hv0 : v ≠ 0) (h3 : 3 ≤ Module.finrank (ZMod 2) V) : ∃ g ∈ rootGroup Q v, g ≠ 1 := by
  have hcard := card_rootGroup hQ hv hv0
  rw [Nat.card_zmod] at hcard
  have hlt : 1 < Nat.card (rootGroup Q v) := by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  haveI : Finite (rootGroup Q v) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp ((Subgroup.one_lt_card_iff_ne_bot _).mp hlt)
  exact ⟨g, g.2, fun h => hg (Subtype.ext h)⟩

theorem exists_mem_rootGroup_apply_ne (hQ : (polarBilin Q).Nondegenerate) {v : V} (hv : Q v = 0)
    (hv0 : v ≠ 0) (h3 : 3 ≤ Module.finrank (ZMod 2) V) {z : V} (hz : z ∉ (ZMod 2) ∙ v) :
    ∃ g ∈ rootGroup Q v, g z ≠ z := by
  by_cases hzv : polar Q z v = 0
  · obtain ⟨u, hu, hzu⟩ := exists_polar_ne_zero_of_not_mem hQ hz
    have hvu : polar Q v u = 0 := mem_orth_span_single_iff.mp hu
    refine ⟨eichler Q v u, eichler_mem_rootGroup hvu, fun h => ?_⟩
    rw [eichler_apply hv hvu, hzv, zero_smul, add_zero, mul_zero, add_zero, sub_eq_self] at h
    rcases zmod2_eq_zero_or_eq_one (polar Q z u) with h0 | h1
    · exact hzu h0
    · rw [h1, one_smul] at h
      exact hv0 h
  · obtain ⟨g, hg, hg1⟩ := exists_mem_rootGroup_ne_one hQ hv hv0 h3
    refine ⟨g, hg, fun h => ?_⟩
    apply sub_not_mem_span_of_mem_rootGroup hQ hv hg hg1 hzv
    rw [h, sub_self]
    exact Submodule.zero_mem _

theorem app_eq_of_mem_pointStabilizer {v : V} (hv0 : v ≠ 0) {s : Gom Q}
    (hs : s ∈ pointStabilizer Q v) : s.app v = v := by
  obtain ⟨c, hc⟩ := mem_pointStabilizer.mp hs
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul] at hc
    exact absurd ((s : V ≃ₗ[ZMod 2] V).injective (hc.trans (map_zero _).symm)) hv0
  · rwa [one_smul] at hc

theorem card_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate) {v : V} (hv0 : v ≠ 0) :
    Nat.card {z : V // polar Q z v = 0} = 2 ^ (Module.finrank (ZMod 2) V - 1) := by
  set f : V →ₗ[ZMod 2] ZMod 2 := (polarBilin Q).flip v with hf
  have hfz : ∀ z, f z = polar Q z v := fun z => rfl
  have hrange : LinearMap.range f = ⊤ := by
    obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hv0
    refine eq_top_iff.mpr fun c _ => ⟨c • y, ?_⟩
    rw [map_smul, hfz, polar_comm, zmod2_eq_one_of_ne_zero hy, smul_eq_mul, mul_one]
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, Module.finrank_self] at hrank
  have hker : Nat.card (LinearMap.ker f) = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker f) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have he : {z : V // polar Q z v = 0} ≃ LinearMap.ker f :=
    Equiv.subtypeEquivRight fun z => by rw [LinearMap.mem_ker, hfz]
  rw [Nat.card_congr he, hker]
  congr 1
  omega

end CFSG.CGT.HaradaParrott80
