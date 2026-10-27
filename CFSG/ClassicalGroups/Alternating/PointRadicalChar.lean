module

public import CFSG.ClassicalGroups.Alternating.PointRadicalNormalizer

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

private theorem gl_inv_apply_apply_pt (g : LinearMap.GeneralLinearGroup K V) (x : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

private theorem eq_one_of_fix_pair (hB : B.IsAlt) {u v : V} (hu1 : B u v = 1)
    {h : LinearMap.GeneralLinearGroup K V}
    (hiso : ∀ x y, B ((h : V →ₗ[K] V) x) ((h : V →ₗ[K] V) y) = B x y)
    (hhu : (h : V →ₗ[K] V) u = u) (hhv : (h : V →ₗ[K] V) v = v)
    (hx : ∀ x, B x v = 0 → ∃ c : K, (h : V →ₗ[K] V) x - x = c • v) :
    h = 1 := by
  have hvu : B v u = -1 := by rw [← hB.neg_eq u v, hu1]
  have hperp : ∀ z, B z u = 0 → B z v = 0 → (h : V →ₗ[K] V) z = z := by
    intro z hzu hzv
    obtain ⟨c, hc⟩ := hx z hzv
    have hhz : B ((h : V →ₗ[K] V) z) u = 0 := by
      have := hiso z u
      rwa [hhu, hzu] at this
    have key : c * B v u = 0 := by
      have h1 : B ((h : V →ₗ[K] V) z - z) u = c * B v u := by
        rw [hc, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← h1, map_sub, LinearMap.sub_apply, hhz, hzu, sub_zero]
    rw [hvu, mul_neg_one, neg_eq_zero] at key
    rw [key, zero_smul, sub_eq_zero] at hc
    exact hc
  refine Units.ext (LinearMap.ext fun y => ?_)
  rw [Units.val_one, Module.End.one_apply]
  obtain ⟨p, hp⟩ : ∃ p : V, p = (B y v) • u - (B y u) • v := ⟨_, rfl⟩
  have hpv : B (y - p) v = 0 := by
    rw [hp]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu1,
      hB.self_eq_zero]
    ring
  have hpu : B (y - p) u = 0 := by
    rw [hp]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hvu,
      hB.self_eq_zero]
    ring
  have hhp : (h : V →ₗ[K] V) p = p := by
    rw [hp, map_sub, map_smul, map_smul, hhu, hhv]
  have hsplit : (h : V →ₗ[K] V) (y - p + p) = y - p + p := by
    rw [map_add, hperp (y - p) hpu hpv, hhp]
  rwa [sub_add_cancel] at hsplit

theorem mem_pointRadical_iff (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {v : V} (hv : v ≠ 0) {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ pointRadical B hB v ↔ g ∈ bilinIsometryGroup B ∧ (g : V →ₗ[K] V) v = v ∧
      ∀ x, B x v = 0 → ∃ c : K, (g : V →ₗ[K] V) x - x = c • v := by
  constructor
  · intro hg
    exact ⟨pointRadical_le_bilinIsometryGroup hB v hg, apply_self_of_mem_pointRadical hB hg,
      fun x hx => (mem_pointRadical_props hB hg).2 x hx⟩
  rintro ⟨hgO, hgv, hgx⟩
  obtain ⟨y, hy⟩ : ∃ y : V, B y v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (hBn.2 v hcon)
  obtain ⟨u, hu1⟩ : ∃ u : V, B u v = 1 :=
    ⟨(B y v)⁻¹ • y, by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  have hgiso := mem_bilinIsometryGroup.mp hgO
  obtain ⟨w, hw⟩ : ∃ w : V, w = (g : V →ₗ[K] V) u - u := ⟨_, rfl⟩
  have hBv : B v w = 0 := by
    have h1 := hgiso v u
    rw [hgv] at h1
    rw [hw, map_sub, h1, sub_self]
  obtain ⟨s, hsdef⟩ : ∃ s : LinearMap.GeneralLinearGroup K V,
      s = siegel B hB v w (-(B u w)) := ⟨_, rfl⟩
  have hs : s ∈ pointRadical B hB v := by
    rw [hsdef]
    exact siegel_mem_pointRadical hB hBv _
  have hsu : (s : V →ₗ[K] V) u = (g : V →ₗ[K] V) u := by
    rw [hsdef, siegel_apply hB hBv, hu1, hw]
    module
  have hsO : s ∈ bilinIsometryGroup B := pointRadical_le_bilinIsometryGroup hB v hs
  have hsinv : s⁻¹ ∈ pointRadical B hB v := inv_mem hs
  have hsinvv : ((s⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v = v :=
    apply_self_of_mem_pointRadical hB hsinv
  have hhO : s⁻¹ * g ∈ bilinIsometryGroup B := mul_mem (inv_mem hsO) hgO
  have hhu : ((s⁻¹ * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u = u := by
    rw [Units.val_mul, Module.End.mul_apply, ← hsu, gl_inv_apply_apply_pt]
  have hhv : ((s⁻¹ * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v = v := by
    rw [Units.val_mul, Module.End.mul_apply, hgv, hsinvv]
  have hhx : ∀ x, B x v = 0 → ∃ c : K,
      ((s⁻¹ * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x - x = c • v := by
    intro x hx
    obtain ⟨c₁, hc₁⟩ := hgx x hx
    obtain ⟨c₂, hc₂⟩ := (mem_pointRadical_props hB hsinv).2 x hx
    refine ⟨c₁ + c₂, ?_⟩
    have hG : (g : V →ₗ[K] V) x = x + c₁ • v := by
      rw [← hc₁]
      abel
    have hS : ((s⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x = x + c₂ • v := by
      rw [← hc₂]
      abel
    rw [Units.val_mul, Module.End.mul_apply, hG, map_add, map_smul, hsinvv, hS]
    module
  have hone : s⁻¹ * g = 1 :=
    eq_one_of_fix_pair hB hu1 (mem_bilinIsometryGroup.mp hhO) hhu hhv hhx
  have hgs : g = s := by
    have h2 : s * (s⁻¹ * g) = g := mul_inv_cancel_left s g
    rw [hone, mul_one] at h2
    exact h2.symm
  rw [hgs]
  exact hs

end CFSG.ClassicalGroups.Alternating
