module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup
open scoped commutatorElement

section SwapNorm

variable {G : Type} [Group G] {A : Type} [CommGroup A]

theorem swap_norm_exists (C C₁ : Subgroup G) (hnorm : ∀ x ∈ C, ∀ c ∈ C₁, x * c * x⁻¹ ∈ C₁)
    (hidx : ∀ x ∈ C, ∀ y ∈ C, x ∉ C₁ → y ∉ C₁ → x * y ∈ C₁)
    {t : G} (htC : t ∈ C) (htn : t ∉ C₁) (ρ : ↥C₁ →* A) :
    ∃ N : ↥C₁ →* A, (∀ c : ↥C₁, ∀ hc : t⁻¹ * (c : G) * t ∈ C₁,
        N c = ρ c * ρ ⟨t⁻¹ * (c : G) * t, hc⟩) ∧
      ∀ x ∈ ⁅C, C⁆, ∃ hx : x ∈ C₁, N ⟨x, hx⟩ = 1 := by
  have hinvt : t⁻¹ ∈ C := C.inv_mem htC
  have hinvtn : t⁻¹ ∉ C₁ := fun h => htn (by simpa using C₁.inv_mem h)
  have hconj : ∀ c ∈ C₁, t⁻¹ * c * t ∈ C₁ := fun c hc => by
    simpa using hnorm t⁻¹ hinvt c hc
  have ht2 : t * t ∈ C₁ := hidx t htC t htC htn htn
  let σ : ↥C₁ →* ↥C₁ :=
    { toFun := fun c => ⟨t⁻¹ * (c : G) * t, hconj c c.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show t⁻¹ * ((x : G) * (y : G)) * t = (t⁻¹ * (x : G) * t) * (t⁻¹ * (y : G) * t)
        group) }
  let N : ↥C₁ →* A := ρ * ρ.comp σ
  have hσσ : ∀ c : ↥C₁, ρ (σ (σ c)) = ρ c := by
    intro c
    have h : σ (σ c) = (⟨t * t, ht2⟩ : ↥C₁)⁻¹ * c * ⟨t * t, ht2⟩ := by
      apply Subtype.ext
      show t⁻¹ * (t⁻¹ * (c : G) * t) * t = (t * t)⁻¹ * (c : G) * (t * t)
      group
    rw [h, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have hNσ : ∀ c : ↥C₁, N (σ c) = N c := by
    intro c
    show ρ (σ c) * ρ (σ (σ c)) = ρ c * ρ (σ c)
    rw [hσσ, mul_comm]
  have hNt : ∀ c : ↥C₁, ∀ hc : t * (c : G) * t⁻¹ ∈ C₁, N ⟨t * (c : G) * t⁻¹, hc⟩ = N c := by
    intro c hc
    have h : σ ⟨t * (c : G) * t⁻¹, hc⟩ = c := by
      apply Subtype.ext
      show t⁻¹ * (t * (c : G) * t⁻¹) * t = (c : G)
      group
    rw [← hNσ ⟨t * (c : G) * t⁻¹, hc⟩, h]
  have hinv : ∀ w ∈ C, ∀ c : ↥C₁, ∀ hw : w * (c : G) * w⁻¹ ∈ C₁,
      N ⟨w * (c : G) * w⁻¹, hw⟩ = N c := by
    intro w hwC c hw
    by_cases hw1 : w ∈ C₁
    · have h : (⟨w * (c : G) * w⁻¹, hw⟩ : ↥C₁) =
          (⟨w, hw1⟩ : ↥C₁) * c * (⟨w, hw1⟩ : ↥C₁)⁻¹ := rfl
      rw [h, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
    · have hc₀ : w * t⁻¹ ∈ C₁ := hidx w hwC t⁻¹ hinvt hw1 hinvtn
      have hc' : t * (c : G) * t⁻¹ ∈ C₁ := hnorm t htC c c.2
      have h : (⟨w * (c : G) * w⁻¹, hw⟩ : ↥C₁) =
          (⟨w * t⁻¹, hc₀⟩ : ↥C₁) * ⟨t * (c : G) * t⁻¹, hc'⟩ * (⟨w * t⁻¹, hc₀⟩ : ↥C₁)⁻¹ := by
        apply Subtype.ext
        show w * (c : G) * w⁻¹ = (w * t⁻¹) * (t * (c : G) * t⁻¹) * (w * t⁻¹)⁻¹
        group
      rw [h, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul, hNt c hc']
  refine ⟨N, fun c hc => rfl, ?_⟩
  have hker : ⁅C, C⁆ ≤ N.ker.map C₁.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    suffices h : ∃ hxy : ⁅x, y⁆ ∈ C₁, N ⟨⁅x, y⁆, hxy⟩ = 1 by
      obtain ⟨hxy, h1⟩ := h
      exact Subgroup.mem_map.2 ⟨⟨⁅x, y⁆, hxy⟩, h1, rfl⟩
    by_cases hx1 : x ∈ C₁
    · have hyx : y * x⁻¹ * y⁻¹ ∈ C₁ := hnorm y hy x⁻¹ (C₁.inv_mem hx1)
      have hxy : ⁅x, y⁆ ∈ C₁ := by
        have : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [this]
        exact C₁.mul_mem hx1 hyx
      refine ⟨hxy, ?_⟩
      have h : (⟨⁅x, y⁆, hxy⟩ : ↥C₁) = ⟨x, hx1⟩ * ⟨y * x⁻¹ * y⁻¹, hyx⟩ := by
        apply Subtype.ext
        show ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹)
        simp only [commutatorElement_def]
        group
      have h2 : N ⟨y * x⁻¹ * y⁻¹, hyx⟩ = (N ⟨x, hx1⟩)⁻¹ := by
        have h3 := hinv y hy (⟨x⁻¹, C₁.inv_mem hx1⟩ : ↥C₁) hyx
        have e : N (⟨x⁻¹, C₁.inv_mem hx1⟩ : ↥C₁) = (N ⟨x, hx1⟩)⁻¹ := by
          rw [← map_inv]
          rfl
        exact h3.trans e
      rw [h, map_mul, h2, mul_inv_cancel]
    · by_cases hy1 : y ∈ C₁
      · have hxyx : x * y * x⁻¹ ∈ C₁ := hnorm x hx y hy1
        have hxy : ⁅x, y⁆ ∈ C₁ := by
          have : ⁅x, y⁆ = (x * y * x⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
          rw [this]
          exact C₁.mul_mem hxyx (C₁.inv_mem hy1)
        refine ⟨hxy, ?_⟩
        have h : (⟨⁅x, y⁆, hxy⟩ : ↥C₁) = ⟨x * y * x⁻¹, hxyx⟩ * (⟨y, hy1⟩ : ↥C₁)⁻¹ := rfl
        have h2 : N ⟨x * y * x⁻¹, hxyx⟩ = N ⟨y, hy1⟩ := hinv x hx ⟨y, hy1⟩ hxyx
        rw [h, map_mul, map_inv, h2, mul_inv_cancel]
      · have hxy1 : x * y ∈ C₁ := hidx x hx y hy hx1 hy1
        have hyx1 : y * x ∈ C₁ := hidx y hy x hx hy1 hx1
        have hxy : ⁅x, y⁆ ∈ C₁ := by
          have : ⁅x, y⁆ = (x * y) * (y * x)⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [this]
          exact C₁.mul_mem hxy1 (C₁.inv_mem hyx1)
        refine ⟨hxy, ?_⟩
        have h : (⟨⁅x, y⁆, hxy⟩ : ↥C₁) = ⟨x * y, hxy1⟩ * (⟨y * x, hyx1⟩ : ↥C₁)⁻¹ := by
          apply Subtype.ext
          show ⁅x, y⁆ = (x * y) * (y * x)⁻¹
          simp only [commutatorElement_def]
          group
        have h2 : N ⟨y * x, hyx1⟩ = N ⟨x * y, hxy1⟩ := by
          have hw : x⁻¹ * ((⟨x * y, hxy1⟩ : ↥C₁) : G) * x⁻¹⁻¹ ∈ C₁ :=
            hnorm x⁻¹ (C.inv_mem hx) _ (⟨x * y, hxy1⟩ : ↥C₁).2
          have e : (⟨x⁻¹ * ((⟨x * y, hxy1⟩ : ↥C₁) : G) * x⁻¹⁻¹, hw⟩ : ↥C₁) = ⟨y * x, hyx1⟩ :=
            Subtype.ext (by
              show x⁻¹ * (x * y) * x⁻¹⁻¹ = y * x
              group)
          rw [← e]
          exact hinv x⁻¹ (C.inv_mem hx) ⟨x * y, hxy1⟩ hw
        rw [h, map_mul, map_inv, h2, mul_inv_cancel]
  intro x hx
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 (hker hx)
  exact ⟨c.2, hc⟩

end SwapNorm

end CFSG.GH74.GLS.IVK.Lifted
