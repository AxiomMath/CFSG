module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.GroupTheory

open scoped Pointwise

theorem permutes_of_map_permutes {H K : Type*} [Group H] [Group K] (f : H →* K)
    {X T : Subgroup H} (hker : f.ker ≤ T)
    (h : (X.map f : Set K) * (T.map f : Set K) = (T.map f : Set K) * (X.map f : Set K)) :
    (X : Set H) * (T : Set H) = (T : Set H) * (X : Set H) := by
  ext z
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    have hmem : f (x * t) ∈ (X.map f : Set K) * (T.map f : Set K) :=
      ⟨f x, Subgroup.mem_map_of_mem f hx, f t, Subgroup.mem_map_of_mem f ht, by rw [map_mul]⟩
    rw [h] at hmem
    obtain ⟨s, hs, y, hy, hsy⟩ := hmem
    obtain ⟨t₁, ht₁, hst⟩ := Subgroup.mem_map.mp hs
    obtain ⟨x₁, hx₁, hxeq⟩ := Subgroup.mem_map.mp hy
    have hq : (x * t) * (t₁ * x₁)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : f (x * t) = f t₁ * f x₁ := by
        rw [← hsy, ← hst, hxeq]
      calc f ((x * t) * (t₁ * x₁)⁻¹)
          = f (x * t) * (f (t₁ * x₁))⁻¹ := by rw [map_mul, map_inv]
        _ = (f t₁ * f x₁) * (f t₁ * f x₁)⁻¹ := by rw [h1, map_mul]
        _ = 1 := mul_inv_cancel _
    have hqT : (x * t) * (t₁ * x₁)⁻¹ ∈ T := hker hq
    refine ⟨(x * t) * (t₁ * x₁)⁻¹ * t₁, T.mul_mem hqT ht₁, x₁, hx₁, ?_⟩
    group
  · rintro ⟨t, ht, x, hx, rfl⟩
    have hmem : f (t * x) ∈ (T.map f : Set K) * (X.map f : Set K) :=
      ⟨f t, Subgroup.mem_map_of_mem f ht, f x, Subgroup.mem_map_of_mem f hx, by rw [map_mul]⟩
    rw [← h] at hmem
    obtain ⟨y, hy, s, hs, hys⟩ := hmem
    obtain ⟨x₁, hx₁, hxeq⟩ := Subgroup.mem_map.mp hy
    obtain ⟨t₁, ht₁, hst⟩ := Subgroup.mem_map.mp hs
    have hq : (t * x) * (x₁ * t₁)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : f (t * x) = f x₁ * f t₁ := by
        rw [← hys, hxeq, ← hst]
      calc f ((t * x) * (x₁ * t₁)⁻¹)
          = f (t * x) * (f (x₁ * t₁))⁻¹ := by rw [map_mul, map_inv]
        _ = (f x₁ * f t₁) * (f x₁ * f t₁)⁻¹ := by rw [h1, map_mul]
        _ = 1 := mul_inv_cancel _
    have hqT : (t * x) * (x₁ * t₁)⁻¹ ∈ T := hker hq
    refine ⟨x₁, hx₁, x₁⁻¹ * ((t * x) * (x₁ * t₁)⁻¹) * x₁ * t₁, ?_, ?_⟩
    · have hconj : x₁⁻¹ * ((t * x) * (x₁ * t₁)⁻¹) * x₁ ∈ f.ker := by
        rw [MonoidHom.mem_ker] at hq ⊢
        calc f (x₁⁻¹ * ((t * x) * (x₁ * t₁)⁻¹) * x₁)
            = (f x₁)⁻¹ * f ((t * x) * (x₁ * t₁)⁻¹) * f x₁ := by simp
          _ = 1 := by rw [hq]; group
      exact T.mul_mem (hker hconj) ht₁
    · group

end CFSG.GroupTheory
