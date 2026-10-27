module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Prelim

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G]

structure Sec4Frame (L T W : Subgroup G) : Prop where
  V_le : gmsV L T ≤ W
  comm_A : ∀ w ∈ W, ∀ a ∈ gmsA L T, w * a = a * w
  le_normalizer : T ≤ normalizer (W : Set G)
  inf_T : W ⊓ T = gmsV L T

namespace Sec4Frame

variable {L T W : Subgroup G}

theorem exists_mul_eq (hW : Sec4Frame L T W) {x : G} (hx : x ∈ W ⊔ T) :
    ∃ w ∈ W, ∃ t ∈ T, w * t = x := by
  obtain ⟨t, ht, w, hw, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hW.le_normalizer (by rwa [sup_comm] at hx)
  exact ⟨t * w * t⁻¹, (mem_normalizer_iff.mp (hW.le_normalizer ht) w).mp hw, t, ht, by group⟩

theorem mul_mem_iff (hW : Sec4Frame L T W) {w t : G} (hw : w ∈ W) (ht : t ∈ T) :
    w * t ∈ W ↔ t ∈ gmsV L T := by
  constructor
  · intro hx
    have htW : t ∈ W := by simpa using mul_mem (inv_mem hw) hx
    rw [← hW.inf_T]
    exact mem_inf.mpr ⟨htW, ht⟩
  · intro htV
    exact mul_mem hw (hW.V_le htV)

theorem sq_mem_V (hW : Sec4Frame L T W) {w t : G} (hw : w ∈ W) (ht : t ∈ T)
    (hx : w * t * (w * t) = 1) : t * t ∈ gmsV L T := by
  rw [← hW.inf_T]
  refine mem_inf.mpr ⟨?_, mul_mem ht ht⟩
  have h1 : t * w * t⁻¹ ∈ W := (mem_normalizer_iff.mp (hW.le_normalizer ht) w).mp hw
  have : t * t = (t * w * t⁻¹)⁻¹ * w⁻¹ := by
    calc t * t = (t * w * t⁻¹)⁻¹ * w⁻¹ * (w * t * (w * t)) := by group
      _ = (t * w * t⁻¹)⁻¹ * w⁻¹ := by rw [hx, mul_one]
  rw [this]
  exact mul_mem (inv_mem h1) (inv_mem hw)

variable [Finite G] {f : ℕ}

theorem mul_mem (hW : Sec4Frame L T W) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {x₁ x₂ : G} (h₁ : x₁ ∈ W ⊔ T)
    (h₂ : x₂ ∈ W ⊔ T) (h₁₁ : x₁ * x₁ = 1) (h₂₂ : x₂ * x₂ = 1) (h₁W : x₁ ∉ W) (h₂W : x₂ ∉ W) :
    x₁ * x₂ ∈ W := by
  obtain ⟨w₁, hw₁, t₁, ht₁, rfl⟩ := hW.exists_mul_eq h₁
  obtain ⟨w₂, hw₂, t₂, ht₂, rfl⟩ := hW.exists_mul_eq h₂
  rw [hW.mul_mem_iff hw₁ ht₁] at h₁W
  rw [hW.mul_mem_iff hw₂ ht₂] at h₂W
  have hs₁ := hW.sq_mem_V hw₁ ht₁ h₁₁
  have hs₂ := hW.sq_mem_V hw₂ ht₂ h₂₂
  have hmul := h.mul_inv_mem_V hf e ht₁ ht₂ h₁W h₂W hs₁ hs₂
  have ht : t₁ * t₂ ∈ gmsV L T := by
    have : t₁ * t₂ = t₁ * t₂⁻¹ * (t₂ * t₂) := by group
    rw [this]
    exact Subgroup.mul_mem _ hmul hs₂
  have hw : w₁ * (t₁ * w₂ * t₁⁻¹) ∈ W :=
    Subgroup.mul_mem _ hw₁ ((mem_normalizer_iff.mp (hW.le_normalizer ht₁) w₂).mp hw₂)
  have : w₁ * t₁ * (w₂ * t₂) = w₁ * (t₁ * w₂ * t₁⁻¹) * (t₁ * t₂) := by group
  rw [this]
  exact Subgroup.mul_mem _ hw (hW.V_le ht)

theorem card_le_two_mul (hW : Sec4Frame L T W) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {E : Subgroup G}
    (hES : E ≤ W ⊔ T) (hE2 : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 2 * Nat.card (E ⊓ W : Subgroup G) := by
  refine card_le_two_mul_of_mul_mem fun x₁ hx₁ x₂ hx₂ h₁ h₂ => mem_inf.mpr
    ⟨Subgroup.mul_mem _ hx₁ hx₂, ?_⟩
  have h₁W : x₁ ∉ W := fun h' => h₁ (mem_inf.mpr ⟨hx₁, h'⟩)
  have h₂W : x₂ ∉ W := fun h' => h₂ (mem_inf.mpr ⟨hx₂, h'⟩)
  exact hW.mul_mem h hf e (hES hx₁) (hES hx₂) (hE2 _ hx₁) (hE2 _ hx₂) h₁W h₂W

theorem card_sq_le_of_involution (hW : Sec4Frame L T W)
    (h : Sec3 G L T) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    (hX : Sec3.Facts L T (2 ^ f)) {x : G} (hx : x ∈ W ⊔ T) (hxx : x * x = 1) (hxW : x ∉ W) :
    Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) ^ 2 ≤ 2 ^ f := by
  obtain ⟨w, hw, t, ht, rfl⟩ := hW.exists_mul_eq hx
  rw [hW.mul_mem_iff hw ht] at hxW
  have hs := hW.sq_mem_V hw ht hxx
  have heq : gmsA L T ⊓ centralizer ({w * t} : Set G) =
      gmsA L T ⊓ centralizer ({t} : Set G) := by
    ext a
    simp only [mem_inf, mem_centralizer_singleton_iff]
    refine and_congr_right fun ha => ?_
    have hwa : w * a = a * w := hW.comm_A w hw a ha
    constructor
    · intro h1
      have : w * (a * t) = w * (t * a) := by
        calc w * (a * t) = a * (w * t) := by rw [← mul_assoc, hwa, mul_assoc]
          _ = w * t * a := h1
          _ = w * (t * a) := by group
      exact mul_left_cancel this
    · intro h1
      calc a * (w * t) = w * (a * t) := by rw [← mul_assoc, ← hwa, mul_assoc]
        _ = w * (t * a) := by rw [h1]
        _ = w * t * a := by group
  rw [heq]
  exact h.card_sq_le hf e hX ht hxW hs

theorem inf_A_bound (hW : Sec4Frame L T W) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    {x : G} (hx : x ∈ W ⊔ T) (hxx : x * x = 1) (hxW : x ∉ W) {D : Subgroup G}
    (hDV : D ≤ gmsV L T) (hDC : D ≤ centralizer ({x} : Set G)) :
    Nat.card D * 2 ^ f ≤ Nat.card (gmsV L T) * Nat.card (D ⊓ gmsA L T : Subgroup G) ∧
      Nat.card (D ⊓ gmsA L T : Subgroup G) ^ 2 ≤ 2 ^ f := by
  refine ⟨?_, ?_⟩
  · have h1 := card_mul_card_le hDV (le_sup_left : gmsA L T ≤ gmsV L T)
    rwa [(hX.sylow h).1] at h1
  · have h1 := hW.card_sq_le_of_involution h hf e hX hx hxx hxW
    have h2 : Nat.card (D ⊓ gmsA L T : Subgroup G) ≤
        Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) :=
      card_le_of_le (le_inf inf_le_right (inf_le_left.trans hDC))
    exact (Nat.pow_le_pow_left h2 2).trans h1

theorem two_mul_card_lt (hW : Sec4Frame L T W) (h : Sec3 G L T)
    (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    {x : G} (hx : x ∈ W ⊔ T) (hxx : x * x = 1) (hxW : x ∉ W) {D : Subgroup G}
    (hDV : D ≤ gmsV L T) (hDC : D ≤ centralizer ({x} : Set G)) :
    2 * Nat.card D < Nat.card (gmsV L T) := by
  by_contra hle
  push Not at hle
  obtain ⟨h1, h2⟩ := hW.inf_A_bound h hf e hX hx hxx hxW hDV hDC
  have hq : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  set Q := 2 ^ f
  set d := Nat.card (D ⊓ gmsA L T : Subgroup G)
  have h3 : Nat.card (gmsV L T) * Q ≤ Nat.card (gmsV L T) * (2 * d) := by
    calc Nat.card (gmsV L T) * Q ≤ 2 * Nat.card D * Q := Nat.mul_le_mul_right Q hle
      _ = 2 * (Nat.card D * Q) := by ring
      _ ≤ 2 * (Nat.card (gmsV L T) * d) := Nat.mul_le_mul_left 2 h1
      _ = Nat.card (gmsV L T) * (2 * d) := by ring
  have h4 := Nat.le_of_mul_le_mul_left h3 Nat.card_pos
  have h6 := Nat.mul_le_mul h4 h4
  have h7 := Nat.mul_le_mul_left Q hq
  have h8 : 2 * d * (2 * d) = 4 * d ^ 2 := by ring
  linarith

end Sec4Frame

end CFSG.ComponentClassification.GMS78
