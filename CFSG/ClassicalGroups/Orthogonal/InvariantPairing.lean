module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap CFSG.Open
open Matrix

section Abstract

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polarBilin_isRefl' : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rwa [polar_comm]

theorem exists_perp_pair_polar_ne_zero [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank K V) {u : V} (hu0 : u ≠ 0) :
    ∃ s w : V, polar Q u s = 0 ∧ polar Q u w = 0 ∧ polar Q s w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set N : Submodule K V := Submodule.span K {u} with hN
  have hmem : ∀ z : V, z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) N ↔ polar Q u z = 0 := by
    intro z
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact h u (Submodule.mem_span_singleton_self u)
    · intro h x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      show polar Q (a • u) z = 0
      rw [polar_smul_left_eq, h, mul_zero]
  have hle : LinearMap.BilinForm.orthogonal (polarBilin Q) N ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q)
        (LinearMap.BilinForm.orthogonal (polarBilin Q) N) := by
    intro m₁ hm₁
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    show polar Q x m₁ = 0
    rw [polar_comm]
    exact hcon m₁ x ((hmem m₁).mp hm₁) ((hmem x).mp hx)
  rw [LinearMap.BilinForm.orthogonal_orthogonal hQ polarBilin_isRefl' N] at hle
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hQ N
  have h3' : Module.finrank K N = 1 := finrank_span_singleton hu0
  omega

theorem additive_eq_zero_of_polar_eq_zero {A : Type*} [AddGroup A] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ Module.finrank K V) {u : V} (hu : Q u = 0)
    (hu0 : u ≠ 0) (g : V →+ A)
    (hg : ∀ w : V, polar Q u w = 0 → ∀ y : V, g (eichler Q u w y) = g y)
    {x : V} (hx : polar Q u x = 0) : g x = 0 := by
  obtain ⟨u₁, hu₁⟩ : ∃ y, polar Q y u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hQ.2 u fun y => by rw [polarBilin_apply_apply]; exact hcon y)
  set u₂ : V := (polar Q u₁ u)⁻¹ • u₁ with hu₂
  have hu₂u : polar Q u₂ u = 1 := by
    rw [hu₂, polar_smul_left_eq, inv_mul_cancel₀ hu₁]
  have key : ∀ y : V, polar Q y u = 1 → ∀ w : V, polar Q u w = 0 →
      g w = g ((polar Q y w + Q w) • u) := by
    intro y hy w hw
    have h1 := hg w hw y
    rw [eichler_apply hu hw y, hy] at h1
    simp only [one_smul, mul_one, map_sub, map_add] at h1
    have h2 : g y + (g w - g ((polar Q y w + Q w) • u)) = g y + 0 := by
      rw [add_zero, ← add_sub_assoc]
      exact h1
    exact sub_eq_zero.mp (add_left_cancel h2)
  have step : ∀ s w : V, polar Q u s = 0 → polar Q u w = 0 → g (polar Q s w • u) = 0 := by
    intro s w hs hw
    have hus : polar Q (u₂ + s) u = 1 := by
      rw [polar_add_left, hu₂u, polar_comm Q s u, hs, add_zero]
    have k1 := key u₂ hu₂u w hw
    have k2 := key (u₂ + s) hus w hw
    have e : (polar Q (u₂ + s) w + Q w) • u =
        (polar Q u₂ w + Q w) • u + polar Q s w • u := by
      rw [polar_add_left]
      module
    rw [k1, e, map_add] at k2
    simpa using k2
  obtain ⟨s₀, w₀, hs₀, hw₀, hsw⟩ := exists_perp_pair_polar_ne_zero hQ h3 hu0
  have lam : ∀ l : K, g (l • u) = 0 := by
    intro l
    have h := step ((l * (polar Q s₀ w₀)⁻¹) • s₀) w₀
      (by rw [polar_smul_right_eq, hs₀, mul_zero]) hw₀
    rwa [polar_smul_left_eq, mul_assoc, inv_mul_cancel₀ hsw, mul_one] at h
  rw [key u₂ hu₂u x hx, lam]

end Abstract

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem ElemMatrixIso.additive_eq_zero_of_range_polar {Y : Type*} [Group Y] {A : Type*}
    [AddGroup A] (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (φ : Y →* GL ι K) (hφ : φ.range = X)
    (g : (ι → K) →+ A) {u : ι → K} (hu : Q u = 0) (hu0 : u ≠ 0)
    (hg : ∀ (y : Y), (φ y).val *ᵥ u = u → ∀ z : ι → K, g ((φ y).val *ᵥ z) = g z)
    {x : ι → K} (hx : polar Q u x = 0) : g x = 0 := by
  refine additive_eq_zero_of_polar_eq_zero hQ h3 hu hu0 g (fun w _ a => ?_) hx
  set e : Gom Q := ⟨eichler Q u w, eichler_mem_elementaryGroup Q u w⟩ with he
  have hA : ((E.equiv.symm e : X) : GL ι K) ∈ φ.range := by
    rw [hφ]
    exact (E.equiv.symm e).2
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp hA
  have happ : ∀ v, eichler Q u w v = (φ y).val *ᵥ v := by
    intro v
    have h1 := E.app (E.equiv.symm e) v
    rw [MulEquiv.apply_symm_apply, ← hy] at h1
    exact h1
  have hfix : (φ y).val *ᵥ u = u := by
    rw [← happ u]
    exact eichler_apply_self u w
  rw [happ a]
  exact hg y hfix a

end Matrix

end CFSG.ClassicalGroups.Orthogonal
