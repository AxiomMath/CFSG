module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.SeitzReduction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K}
  {B : V →ₛₗ[σ] V →ₗ[K] K}

namespace SesqShear

theorem exists_apply_eq_one (hB : B.SeparatingLeft) {w : V} (hw : w ≠ 0) : ∃ x, B w x = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, B w x ≠ 0 := by
    by_contra! h
    exact hw (hB w h)
  exact ⟨(B w x)⁻¹ • x, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]⟩

end SesqShear

open SesqShear

theorem sesq_shear_rigidity (hB : B.SeparatingLeft) {W L : Submodule K V}
    (hσW : (∃ a, σ a ≠ a) ∨ ∃ w₁ ∈ W, ∃ w₂ ∈ W, LinearIndependent K ![w₁, w₂])
    (hL : L = W.orthogonalBilin B) (hW : W = L.orthogonalBilin B) (hW0 : W ≠ ⊥) (hLW : ¬L ≤ W)
    {φ : K →+* K} {μ : K} (hμ : μ ≠ 0) (T : V →+ V)
    (hT : ∀ (a : K) (v : V), T (a • v) = φ a • T v)
    (hTB : ∀ x y, B (T x) (T y) = μ * φ (B x y)) (hTL : ∀ v ∈ L, T v ∈ L)
    (hsh : ∀ w ∈ W, ∀ u ∈ L, ∃ g : V →ₗ[K] V, (∀ v, T (g v) = g (T v)) ∧
      (∀ v ∈ L, g v = v - B u v • w) ∧ ∀ v, g v - v - B w v • u ∈ W) :
    (∀ a, φ a = a) ∧ ∃ c : K, c ≠ 0 ∧ σ c * c = μ ∧ (∀ v ∈ L, T v = c • v) ∧
      ∀ v, T v - c • v ∈ W := by
  have hLm : ∀ v, v ∈ L ↔ ∀ w ∈ W, B w v = 0 := fun v => by
    rw [hL]
    exact Submodule.mem_orthogonalBilin
  have hWm : ∀ v, v ∈ W ↔ ∀ x ∈ L, B x v = 0 := fun v => by
    rw [hW]
    exact Submodule.mem_orthogonalBilin
  obtain ⟨x₀, hx₀L, hx₀W⟩ := IsConcreteLE.not_le_iff_exists.mp hLW
  obtain ⟨u₀, hu₀L, hu₀⟩ : ∃ u₀ ∈ L, B u₀ x₀ ≠ 0 := by
    by_contra! h
    exact hx₀W ((hWm x₀).mpr h)
  obtain ⟨x₁, hx₁L, hx₁W, hu₀x₁⟩ : ∃ x₁ ∈ L, x₁ ∉ W ∧ B u₀ x₁ = 1 :=
    ⟨(B u₀ x₀)⁻¹ • x₀, L.smul_mem _ hx₀L,
      fun h => hx₀W ((W.smul_mem_iff (inv_ne_zero hu₀)).mp h),
      by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu₀]⟩
  obtain ⟨c, hc⟩ : ∃ c, B u₀ (T x₁) = c := ⟨_, rfl⟩
  have hTW : ∀ w ∈ W, T w = c • w := by
    intro w hw
    obtain ⟨g, hgT, hg1, -⟩ := hsh w hw u₀ hu₀L
    have h1 := hgT x₁
    rw [hg1 x₁ hx₁L, hg1 (T x₁) (hTL x₁ hx₁L), map_sub, hT, hu₀x₁, map_one, one_smul, hc] at h1
    exact sub_right_injective h1
  obtain ⟨w₀, hw₀W, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨y₀, hy₀⟩ := exists_apply_eq_one hB hw₀0
  have hc0 : c ≠ 0 := by
    intro hc0
    have h1 := hTB w₀ y₀
    rw [hTW w₀ hw₀W, hc0, zero_smul, map_zero, LinearMap.zero_apply, hy₀, map_one,
      mul_one] at h1
    exact hμ h1.symm
  have hφ : ∀ a, φ a = a := by
    intro a
    have h1 := hTW (a • w₀) (W.smul_mem a hw₀W)
    rw [hT, hTW w₀ hw₀W, smul_smul, smul_smul] at h1
    exact mul_right_cancel₀ hc0 ((smul_left_injective K hw₀0 h1).trans (mul_comm c a))
  have hTl : ∀ (a : K) (v : V), T (a • v) = a • T v := fun a v => by rw [hT, hφ]
  have hTB' : ∀ x y, B (T x) (T y) = μ * B x y := fun x y => by rw [hTB, hφ]
  have hTLW : ∀ x ∈ L, T x - c • x ∈ W := by
    intro x hx
    refine (hWm _).mpr fun u hu => ?_
    obtain ⟨g, hgT, hg1, -⟩ := hsh w₀ hw₀W u hu
    have h1 := hgT x
    rw [hg1 x hx, hg1 (T x) (hTL x hx), map_sub, hTl, hTW w₀ hw₀W, smul_smul] at h1
    have h2 := smul_left_injective K hw₀0 (sub_right_injective h1)
    rw [map_sub, map_smul, smul_eq_mul, ← h2, mul_comm, sub_self]
  have hstep3 : ∀ w ∈ W, ∀ v, B w (T v) = c * B w v := by
    intro w hw v
    obtain ⟨g, hgT, -, hg2⟩ := hsh w hw x₁ hx₁L
    have hz := hg2 v
    have hmem : (c * B w v - B w (T v)) • x₁ ∈ W := by
      have e2 : T (g v - v - B w v • x₁) = c • (g v - v - B w v • x₁) := hTW _ hz
      rw [map_sub, map_sub, hTl, hgT] at e2
      have e : (c * B w v - B w (T v)) • x₁ = (g (T v) - T v - B w (T v) • x₁) -
          c • (g v - v - B w v • x₁) - B w v • (T x₁ - c • x₁) := by
        linear_combination (norm := module) -e2
      rw [e]
      exact sub_mem (sub_mem (hg2 (T v)) (W.smul_mem c hz)) (W.smul_mem _ (hTLW x₁ hx₁L))
    by_contra hne
    exact hx₁W ((W.smul_mem_iff (sub_ne_zero.mpr (Ne.symm hne))).mp hmem)
  have hXL : ∀ v, T v - c • v ∈ L := fun v => (hLm _).mpr fun w hw => by
    rw [map_sub, map_smul, smul_eq_mul, hstep3 w hw v, sub_self]
  have hμc : σ c * c = μ := by
    have h1 := hTB' w₀ y₀
    rw [hTW w₀ hw₀W, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hstep3 w₀ hw₀W y₀, hy₀,
      mul_one, mul_one] at h1
    exact h1
  have hXu : ∀ w ∈ W, ∀ y, B w y = 1 → ∀ u ∈ L,
      T u - c • u = -B u (T y - c • y) • w := by
    intro w hw y hy u hu
    obtain ⟨g, hgT, hg1, hg2⟩ := hsh w hw u hu
    have h1 : g (T y - c • y) = T (g y) - c • g y := by rw [map_sub, map_smul, hgT]
    rw [hg1 _ (hXL y)] at h1
    have h2 : T (g y - y - B w y • u) = c • (g y - y - B w y • u) := hTW _ (hg2 y)
    rw [map_sub, map_sub, hTl, hy] at h2
    simp only [one_smul] at h2
    linear_combination (norm := module) -h1 - h2
  have hTLc : ∀ u ∈ L, T u = c • u := by
    intro u hu
    rw [← sub_eq_zero]
    rcases hσW with ⟨a, ha⟩ | ⟨w₁, hw₁, w₂, hw₂, hli⟩
    ·
      have e1 := hXu w₀ hw₀W y₀ hy₀ u hu
      have e2 := hXu w₀ hw₀W y₀ hy₀ (a • u) (L.smul_mem a hu)
      have e3 : T (a • u) - c • (a • u) = a • (T u - c • u) := by
        rw [hTl, smul_sub, smul_comm]
      rw [e3, e1, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at e2
      have e4 : ((a - σ a) * B u (T y₀ - c • y₀)) • w₀ = 0 := by
        linear_combination (norm := module) -e2
      have e5 : B u (T y₀ - c • y₀) = 0 :=
        (mul_eq_zero.mp ((smul_eq_zero.mp e4).resolve_right hw₀0)).resolve_left
          (sub_ne_zero.mpr (Ne.symm ha))
      rw [e1, e5, neg_zero, zero_smul]
    ·
      have hw₁0 : w₁ ≠ 0 := by simpa using hli.ne_zero 0
      have hw₂0 : w₂ ≠ 0 := by simpa using hli.ne_zero 1
      obtain ⟨y₁, hy₁⟩ := exists_apply_eq_one hB hw₁0
      obtain ⟨y₂, hy₂⟩ := exists_apply_eq_one hB hw₂0
      have e1 := hXu w₁ hw₁ y₁ hy₁ u hu
      have e2 := hXu w₂ hw₂ y₂ hy₂ u hu
      obtain ⟨h0, -⟩ := hli.eq_zero_of_pair' (e1.symm.trans e2)
      rw [e1, h0, zero_smul]
  refine ⟨hφ, c, hc0, hμc, hTLc, fun v => (hWm _).mpr fun y hy => ?_⟩
  have h1 := hTB' y v
  rw [hTLc y hy, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, ← hμc, mul_assoc] at h1
  have h2 := mul_left_cancel₀ ((map_ne_zero σ).mpr hc0) h1
  rw [map_sub, map_smul, smul_eq_mul, h2, sub_self]

namespace SesqShear

theorem apply_sub_smul_eq_smul {W L : Submodule K V} (hWL : W ≤ L) {T : V →+ V} {c : K}
    (hTL : ∀ v ∈ L, T v = c • v) (hTW : ∀ v, T v - c • v ∈ W) (v : V) :
    T (T v - c • v) = c • (T v - c • v) :=
  hTL _ (hWL (hTW v))

theorem apply_apply_eq_mul_self_smul [CharP K 2] {W L : Submodule K V} (hWL : W ≤ L)
    {T : V →+ V} {c : K} (hTc : ∀ v, T (c • v) = c • T v) (hTL : ∀ v ∈ L, T v = c • v)
    (hTW : ∀ v, T v - c • v ∈ W) (v : V) : T (T v) = (c * c) • v := by
  have h1 := apply_sub_smul_eq_smul hWL hTL hTW v
  rw [map_sub, hTc] at h1
  have h3 : (2 : K) • (c • T v) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  have h4 : (2 : K) • ((c * c) • v) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  linear_combination (norm := module) h1 + h3 - h4

end SesqShear

end CFSG.SeitzReduction
