module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.LinearAlgebra.Reflection

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

theorem exists_bilin_ne_zero_of_finrank_add_one (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) {H : Submodule k V}
    (hH : Module.finrank k H + 1 = Module.finrank k V)
    (hdim : 3 ≤ Module.finrank k V) :
    ∃ x ∈ H, ∃ y ∈ H, B x y ≠ 0 := by
  by_contra h
  push Not at h
  have hle : H ≤ B.orthogonal H := fun x hx =>
    LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => h y hy x hx
  have h1 : Module.finrank k H ≤ Module.finrank k (B.orthogonal H) :=
    Submodule.finrank_mono hle
  have h2 : Module.finrank k (B.orthogonal H) = Module.finrank k V - Module.finrank k H :=
    LinearMap.BilinForm.finrank_orthogonal hB H
  omega

theorem sq_eq_one_of_smul_of_preserves (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) {w s : Module.End k V} {c : k}
    (hw : ∀ x y, B (w x) (w y) = B x y)
    (hs : ∀ x, s x = c • w x)
    (hfix : Module.finrank k (LinearMap.ker (s - 1)) + 1 = Module.finrank k V)
    (hdim : 3 ≤ Module.finrank k V) : c ^ 2 = 1 := by
  obtain ⟨v, hv, u, hu, hvu⟩ :=
    exists_bilin_ne_zero_of_finrank_add_one B hB hfix hdim
  have hsv : s v = v := by
    have h := LinearMap.mem_ker.1 hv
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  have hsu : s u = u := by
    have h := LinearMap.mem_ker.1 hu
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  have hv' : v = c • w v := hsv.symm.trans (hs v)
  have hu' : u = c • w u := hsu.symm.trans (hs u)
  have hkey : B v u = c ^ 2 * B v u := by
    have h1 : B v u = B (c • w v) (c • w u) := by
      conv_lhs => rw [hv', hu']
    have h2 : B (c • w v) (c • w u) = c • B (w v) (c • w u) := by
      rw [map_smul B c (w v), LinearMap.smul_apply]
    have h3 : B (w v) (c • w u) = c • B (w v) (w u) :=
      map_smul (B (w v)) c (w u)
    conv_lhs => rw [h1, h2, h3, smul_smul, smul_eq_mul, hw]
    ring
  have hpoly : (1 - c ^ 2) * B v u = 0 := by
    have h : B v u - c ^ 2 * B v u = 0 := sub_eq_zero.2 hkey
    calc (1 - c ^ 2) * B v u = B v u - c ^ 2 * B v u := by rw [sub_mul, one_mul]
      _ = 0 := h
  have hc : 1 - c ^ 2 = 0 := (mul_eq_zero.1 hpoly).resolve_right hvu
  exact (sub_eq_zero.1 hc).symm

theorem eq_one_or_eq_neg_one_of_smul_of_preserves (B : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) {w s : Module.End k V} {c : k}
    (hw : ∀ x y, B (w x) (w y) = B x y)
    (hs : ∀ x, s x = c • w x)
    (hfix : Module.finrank k (LinearMap.ker (s - 1)) + 1 = Module.finrank k V)
    (hdim : 3 ≤ Module.finrank k V) : c = 1 ∨ c = -1 :=
  sq_eq_one_iff.1 (sq_eq_one_of_smul_of_preserves B hB hw hs hfix hdim)

end CFSG.LinearAlgebra.Reflection

end
