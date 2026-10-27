module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open Subgroup

variable {G : Type*} [Group G]

structure IsNSC (S F : Subgroup G) (k : ℕ) : Prop where
  le : F ≤ S
  normal : ∀ s ∈ S, ∀ f ∈ F, s * f * s⁻¹ ∈ F
  comm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x
  mul_self : ∀ x ∈ F, x * x = 1
  card_eq : Nat.card F = k
  self_centralizing : ∀ s ∈ S, (∀ f ∈ F, s * f = f * s) → s ∈ F

@[expose] def imageEquiv {M : Type*} [Group M] {S : Subgroup G} {S' : Subgroup M} (e : S ≃* S')
    (F : Subgroup G) : Subgroup M :=
  ((F.subgroupOf S).map e.toMonoidHom).map S'.subtype

variable {M : Type*} [Group M] {S : Subgroup G} {S' : Subgroup M} (e : S ≃* S')

theorem mem_imageEquiv {F : Subgroup G} {y : M} :
    y ∈ imageEquiv e F ↔ ∃ x : S, (x : G) ∈ F ∧ ((e x : S') : M) = y := by
  simp only [imageEquiv, mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom, coe_subtype]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, rfl⟩

theorem imageEquiv_le (F : Subgroup G) : imageEquiv e F ≤ S' := by
  intro y hy
  obtain ⟨x, -, rfl⟩ := (mem_imageEquiv e).1 hy
  exact (e x).2

theorem card_imageEquiv {F : Subgroup G} (hF : F ≤ S) :
    Nat.card (imageEquiv e F) = Nat.card F := by
  rw [imageEquiv, card_map_of_injective S'.subtype_injective,
    card_map_of_injective e.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hF).toEquiv

theorem IsNSC.map_equiv {F : Subgroup G} {k : ℕ} (h : IsNSC S F k) :
    IsNSC S' (imageEquiv e F) k where
  le := imageEquiv_le e F
  normal := by
    intro s hs f hf
    obtain ⟨x, hx, rfl⟩ := (mem_imageEquiv e).1 hf
    set s₀ := e.symm ⟨s, hs⟩
    have hs₀ : ((e s₀ : S') : M) = s := by simp [s₀]
    refine (mem_imageEquiv e).2 ⟨s₀ * x * s₀⁻¹, ?_, ?_⟩
    · exact h.normal _ s₀.2 _ hx
    · rw [map_mul, map_mul, map_inv]
      simp only [coe_mul, coe_inv, hs₀]
  comm := by
    intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := (mem_imageEquiv e).1 hy
    obtain ⟨w, hw, rfl⟩ := (mem_imageEquiv e).1 hz
    have hxw : x * w = w * x := Subtype.ext (h.comm _ hx _ hw)
    rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, hxw]
  mul_self := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_imageEquiv e).1 hy
    have hxx : x * x = 1 := Subtype.ext (h.mul_self _ hx)
    rw [← coe_mul, ← map_mul, hxx, map_one, coe_one]
  card_eq := by rw [card_imageEquiv e h.le, h.card_eq]
  self_centralizing := by
    intro s hs hc
    set s₀ := e.symm ⟨s, hs⟩
    have hs₀ : ((e s₀ : S') : M) = s := by simp [s₀]
    refine (mem_imageEquiv e).2 ⟨s₀, h.self_centralizing _ s₀.2 fun f hf => ?_, hs₀⟩
    have h1 := hc ((e ⟨f, h.le hf⟩ : S') : M) ((mem_imageEquiv e).2 ⟨⟨f, h.le hf⟩, hf, rfl⟩)
    rw [← hs₀, ← coe_mul, ← coe_mul, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective (Subtype.ext h1))

include e in
theorem IsNSC.eq_of_equiv {k : ℕ}
    (huniq : ∀ F₁ F₂ : Subgroup M, IsNSC S' F₁ k → IsNSC S' F₂ k → F₁ = F₂)
    {F₁ F₂ : Subgroup G} (h₁ : IsNSC S F₁ k) (h₂ : IsNSC S F₂ k) : F₁ = F₂ := by
  have himg := huniq _ _ (h₁.map_equiv e) (h₂.map_equiv e)
  have key : ∀ {A B : Subgroup G}, IsNSC S A k → IsNSC S B k → imageEquiv e A = imageEquiv e B →
      A ≤ B := by
    intro A B hA hB hAB x hx
    have hy : ((e ⟨x, hA.le hx⟩ : S') : M) ∈ imageEquiv e B :=
      hAB ▸ (mem_imageEquiv e).2 ⟨⟨x, hA.le hx⟩, hx, rfl⟩
    obtain ⟨w, hw, hwx⟩ := (mem_imageEquiv e).1 hy
    have : w = ⟨x, hA.le hx⟩ := e.injective (Subtype.ext hwx)
    rw [this] at hw
    exact hw
  exact le_antisymm (key h₁ h₂ himg) (key h₂ h₁ himg.symm)

end CFSG.EvenSmallLie.OmegaEight.SplitC
