module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Swap

open Module CFSG.EvenSporadicStandard.HNRecog.Fpf

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def SwapsFactors (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (b : V ≃ₗ[ZMod 2] V) : Prop :=
  (∀ x : A5, ∃ y : A5, b * σ (x, 1) * b⁻¹ = σ (1, y)) ∧
    (∀ y : A5, ∃ x : A5, b * σ (1, y) * b⁻¹ = σ (x, 1))

@[expose] def PreservesFactors (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (u : V ≃ₗ[ZMod 2] V) : Prop :=
  (∀ x : A5, ∃ x' : A5, u * σ (x, 1) * u⁻¹ = σ (x', 1)) ∧
    (∀ y : A5, ∃ y' : A5, u * σ (1, y) * u⁻¹ = σ (1, y'))

variable {σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)} {b b' : V ≃ₗ[ZMod 2] V}

private theorem sigma_conj_eq (h u : A5 × A5) :
    σ h * σ u * (σ h)⁻¹ = σ (h * u * h⁻¹) := by
  rw [← map_inv, ← map_mul, ← map_mul]

private theorem sigma_inv_conj_eq (h u : A5 × A5) :
    (σ h)⁻¹ * σ u * σ h = σ (h⁻¹ * u * h) := by
  rw [← map_inv, ← map_mul, ← map_mul]

theorem SwapsFactors.conj (hb : SwapsFactors σ b) (h : A5 × A5) :
    SwapsFactors σ (σ h * b * (σ h)⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := hb.1 (h.1⁻¹ * x * h.1)
    refine ⟨h.2 * y * h.2⁻¹, ?_⟩
    have key : (σ h)⁻¹ * σ (x, 1) * σ h = σ (h.1⁻¹ * x * h.1, 1) := by
      rw [sigma_inv_conj_eq]
      congr 1
      ext <;> simp [Prod.mk_mul_mk, mul_assoc]
    calc (σ h * b * (σ h)⁻¹) * σ (x, 1) * (σ h * b * (σ h)⁻¹)⁻¹
        = σ h * (b * ((σ h)⁻¹ * σ (x, 1) * σ h) * b⁻¹) * (σ h)⁻¹ := by
          group
      _ = σ h * (b * σ (h.1⁻¹ * x * h.1, 1) * b⁻¹) * (σ h)⁻¹ := by rw [key]
      _ = σ h * σ (1, y) * (σ h)⁻¹ := by rw [hy]
      _ = σ (1, h.2 * y * h.2⁻¹) := by
          rw [sigma_conj_eq]
          congr 1
          ext <;> simp [Prod.mk_mul_mk, mul_assoc]
  · intro y
    obtain ⟨x, hx⟩ := hb.2 (h.2⁻¹ * y * h.2)
    refine ⟨h.1 * x * h.1⁻¹, ?_⟩
    have key : (σ h)⁻¹ * σ (1, y) * σ h = σ (1, h.2⁻¹ * y * h.2) := by
      rw [sigma_inv_conj_eq]
      congr 1
      ext <;> simp [Prod.mk_mul_mk, mul_assoc]
    calc (σ h * b * (σ h)⁻¹) * σ (1, y) * (σ h * b * (σ h)⁻¹)⁻¹
        = σ h * (b * ((σ h)⁻¹ * σ (1, y) * σ h) * b⁻¹) * (σ h)⁻¹ := by
          group
      _ = σ h * (b * σ (1, h.2⁻¹ * y * h.2) * b⁻¹) * (σ h)⁻¹ := by rw [key]
      _ = σ h * σ (x, 1) * (σ h)⁻¹ := by rw [hx]
      _ = σ (h.1 * x * h.1⁻¹, 1) := by
          rw [sigma_conj_eq]
          congr 1
          ext <;> simp [Prod.mk_mul_mk, mul_assoc]

theorem SwapsFactors.mul (hb : SwapsFactors σ b) (hb' : SwapsFactors σ b') :
    PreservesFactors σ (b * b') := by
  refine ⟨?_, ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := hb'.1 x
    obtain ⟨x', hx'⟩ := hb.2 y
    refine ⟨x', ?_⟩
    calc (b * b') * σ (x, 1) * (b * b')⁻¹
        = b * (b' * σ (x, 1) * b'⁻¹) * b⁻¹ := by group
      _ = b * σ (1, y) * b⁻¹ := by rw [hy]
      _ = σ (x', 1) := hx'
  · intro y
    obtain ⟨x, hx⟩ := hb'.2 y
    obtain ⟨y', hy'⟩ := hb.1 x
    refine ⟨y', ?_⟩
    calc (b * b') * σ (1, y) * (b * b')⁻¹
        = b * (b' * σ (1, y) * b'⁻¹) * b⁻¹ := by group
      _ = b * σ (x, 1) * b⁻¹ := by rw [hx]
      _ = σ (1, y') := hy'

theorem finrank_range_conj (g b : V ≃ₗ[ZMod 2] V) :
    finrank (ZMod 2) (LinearMap.range (((g * b * g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) + 1)) =
      finrank (ZMod 2) (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1)) := by
  have h : (((g * b * g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) + 1)
      = (g : V →ₗ[ZMod 2] V) ∘ₗ (((b : V →ₗ[ZMod 2] V) + 1) ∘ₗ ((g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)) := by
    ext v
    simp [Module.End.mul_apply]
  rw [h, LinearMap.range_comp, LinearMap.range_comp]
  rw [LinearEquiv.range, Submodule.map_top]
  exact LinearEquiv.finrank_map_eq g (LinearMap.range ((b : V →ₗ[ZMod 2] V) + 1))

theorem exists_conj_normalized (hσ : Function.Injective σ) (hb : b * b = 1)
    (hsw : SwapsFactors σ b) :
    ∃ (z : A5) (k : ℕ), (k = 1 ∨ k = 2) ∧
      (σ (1, z⁻¹) * b * (σ (1, z⁻¹))⁻¹) * σ (a₀, 1) * (σ (1, z⁻¹) * b * (σ (1, z⁻¹))⁻¹)⁻¹ =
        σ (1, a₀ ^ k) := by
  obtain ⟨y, hy⟩ := hsw.1 a₀
  have hinr : Function.Injective (MonoidHom.inr A5 A5) := by
    intro a b h
    simpa [MonoidHom.inr_apply] using congr_arg Prod.snd h
  have horder_a : orderOf (σ (a₀, 1)) = 5 := by
    rw [orderOf_injective σ hσ (a₀, 1), Prod.orderOf_mk, orderOf_a₀]
    simp
  have hsemi : SemiconjBy b (σ (a₀, 1)) (σ (1, y)) := by
    show b * σ (a₀, 1) = σ (1, y) * b
    calc b * σ (a₀, 1) = b * σ (a₀, 1) * b⁻¹ * b := by group
      _ = σ (1, y) * b := by rw [hy]
  have hy5 : orderOf y = 5 := by
    rw [← orderOf_injective (σ.comp (MonoidHom.inr A5 A5)) (hσ.comp hinr) y]
    change orderOf (σ (1, y)) = 5
    rw [← SemiconjBy.orderOf_eq b hsemi, horder_a]
  obtain ⟨z, k, hk, hzy⟩ := exists_conj_of_orderOf_eq_five hy5
  refine ⟨z, k, hk, ?_⟩
  have key : (σ (1, z⁻¹))⁻¹ * σ (a₀, 1) * σ (1, z⁻¹) = σ (a₀, 1) := by
    rw [sigma_inv_conj_eq]
    congr 1
    ext <;> simp [Prod.mk_mul_mk, mul_assoc]
  have key2 : σ (1, z⁻¹) * σ (1, y) * (σ (1, z⁻¹))⁻¹ = σ (1, a₀ ^ k) := by
    rw [sigma_conj_eq]
    congr 1
    ext <;> simp [hzy, Prod.mk_mul_mk, mul_assoc]
  calc (σ (1, z⁻¹) * b * (σ (1, z⁻¹))⁻¹) * σ (a₀, 1) * (σ (1, z⁻¹) * b * (σ (1, z⁻¹))⁻¹)⁻¹
      = σ (1, z⁻¹) * (b * ((σ (1, z⁻¹))⁻¹ * σ (a₀, 1) * σ (1, z⁻¹)) * b⁻¹) * (σ (1, z⁻¹))⁻¹ := by
        group
    _ = σ (1, z⁻¹) * (b * σ (a₀, 1) * b⁻¹) * (σ (1, z⁻¹))⁻¹ := by rw [key]
    _ = σ (1, z⁻¹) * σ (1, y) * (σ (1, z⁻¹))⁻¹ := by rw [hy]
    _ = σ (1, a₀ ^ k) := key2

end CFSG.EvenSporadicStandard.HNRecog.Swap
