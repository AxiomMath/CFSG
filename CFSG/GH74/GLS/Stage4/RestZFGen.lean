module

public import CFSG.GH74.GLS.Stage4.RestZFKit
public import CFSG.GH74.GLS.Stage4.RestZA
public import CFSG.GH74.GLS.Stage4.LocalRankOne
public import CFSG.GH74.GLS.Stage4.T2SL2A

public section

namespace CFSG.GH74.GLS.Stage4.Rest.ZF

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Rest Subgroup

variable {G : Type} [Group G]

theorem kit_of_phi {H : Subgroup G} {r u z : G} {Ya Yb : Subgroup G}
    (hP : SL2Phi H r Ya Yb) (hodd : Odd (Nat.card Ya))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (huH : u ∈ H) (huu : u * u = 1)
    (hHa : ∀ h ∈ H, ∀ x ∈ Ya, h * x * h⁻¹ ∈ Ya) (hHb : ∀ h ∈ H, ∀ x ∈ Yb, h * x * h⁻¹ ∈ Yb)
    (hnc : ∀ x ∈ Ya, x ≠ 1 → u * x * u⁻¹ ≠ x)
    (hinv : ∀ x ∈ Ya ⊔ Yb, x * x = 1 → x = 1 ∨ x = z) :
    ∃ W k : G, W ∈ Ya ⊔ Yb ∧ k ∈ Ya ⊔ Yb ∧ W * W = z ∧ (∃ g ∈ H, W = r * g) ∧
      u * k * u⁻¹ = W * k ∧ u * W * u⁻¹ = z * W := by
  obtain ⟨F, hF, hFin, hc, φ, hφ, hU, hL, hD, g₀, hg₀, hW⟩ := hP
  have hodd' : Odd (Nat.card F) := by rw [hc]; exact hodd
  have h2 : (2 : F) ≠ 0 := ZA.two_ne_zero_of_card_odd hodd'
  have hUm : ∀ c, φ (sl2U c) ∈ Ya := fun c => (hU _).2 ⟨c, rfl⟩
  have hLm : ∀ c, φ (sl2L c) ∈ Yb := fun c => (hL _).2 ⟨c, rfl⟩
  have hU' : ∀ c, ∃ d, u * φ (sl2U c) * u⁻¹ = φ (sl2U d) := fun c => by
    obtain ⟨d, hd⟩ := (hU _).1 (hHa u huH _ (hUm c))
    exact ⟨d, hd.symm⟩
  have hL' : ∀ c, ∃ d, u * φ (sl2L c) * u⁻¹ = φ (sl2L d) := fun c => by
    obtain ⟨d, hd⟩ := (hL _).1 (hHb u huH _ (hLm c))
    exact ⟨d, hd.symm⟩
  have hU1 : φ (sl2U 1) ≠ 1 := by
    intro h
    have : sl2U (1 : F) = sl2U 0 := by
      apply hφ; rw [h, sl2U_zero, map_one]
    exact one_ne_zero (sl2U_injective this)
  obtain ⟨hk, hWu⟩ := sl2_u_kit h2 φ hφ hHcomm hD huH huu hU' hL' (hnc _ (hUm 1) hU1)
  have hWmem : φ (sl2W F) ∈ Ya ⊔ Yb := by
    rw [sl2W_eq_ULU, map_mul, map_mul]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (hUm _)) (Subgroup.mem_sup_right (hLm _)))
      (Subgroup.mem_sup_left (hUm _))
  have hkmem : φ (sl2L 1 * sl2U (-(2⁻¹ : F))) ∈ Ya ⊔ Yb := by
    rw [map_mul]
    exact mul_mem (Subgroup.mem_sup_right (hLm _)) (Subgroup.mem_sup_left (hUm _))
  have hDsq : φ (sl2D (-1 : Fˣ)) = φ (sl2W F) * φ (sl2W F) := by
    rw [← map_mul, sl2W_mul_self]
  have hD1 : φ (sl2D (-1 : Fˣ)) * φ (sl2D (-1 : Fˣ)) = 1 := by
    rw [← map_mul, T2.sl2D_mul]
    have : ((-1 : Fˣ) * (-1 : Fˣ)) = 1 := by simp
    rw [this, T2.sl2D_one, map_one]
  have hDne : φ (sl2D (-1 : Fˣ)) ≠ 1 := by
    intro h
    have h' : (sl2D (-1 : Fˣ) : SL2 F) = 1 := by apply hφ; rw [h, map_one]
    have := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h'
    simp at this
    apply h2
    linear_combination -this
  have hDz : φ (sl2D (-1 : Fˣ)) = z := by
    have hmem : φ (sl2D (-1 : Fˣ)) ∈ Ya ⊔ Yb := by rw [hDsq]; exact mul_mem hWmem hWmem
    rcases hinv _ hmem hD1 with h | h
    · exact absurd h hDne
    · exact h
  refine ⟨φ (sl2W F), φ (sl2L 1 * sl2U (-(2⁻¹ : F))), hWmem, hkmem, ?_, ⟨g₀, hg₀, hW⟩, hk, ?_⟩
  · rw [← hDsq, hDz]
  · rw [hWu, hDz]

theorem aW_mem {H : Subgroup G} {a w₁ w₂ W₁ W₂ : G} (ha : a ∈ normalizer (H : Set G))
    (hw₁ : w₁ ∈ normalizer (H : Set G)) (hw₂ : w₂ ∈ normalizer (H : Set G))
    (h₁ : ∃ h ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * h) (h₂ : ∃ h ∈ H, w₂ * a * w₂⁻¹ = a⁻¹ * h)
    (hW₁ : ∃ g ∈ H, W₁ = w₁ * g) (hW₂ : ∃ g ∈ H, W₂ = w₂ * g) :
    ∃ h ∈ H, a * (W₁ * W₂) * a⁻¹ = (W₁ * W₂) * h := by
  have hN : (H.subgroupOf (normalizer (H : Set G))).Normal := Subgroup.normal_in_normalizer
  let π : ↥(normalizer (H : Set G)) →* ↥(normalizer (H : Set G)) ⧸
      H.subgroupOf (normalizer (H : Set G)) := QuotientGroup.mk' _
  have hπ : ∀ x y : ↥(normalizer (H : Set G)), π x = π y ↔ (x : G)⁻¹ * (y : G) ∈ H :=
    fun x y => by
      show (QuotientGroup.mk x : _ ⧸ _) = QuotientGroup.mk y ↔ _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
  have hπ1 : ∀ x : ↥(normalizer (H : Set G)), π x = 1 ↔ (x : G) ∈ H := fun x => by
    show (QuotientGroup.mk x : _ ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hHn : H ≤ normalizer (H : Set G) := Subgroup.le_normalizer
  obtain ⟨g₁, hg₁, rfl⟩ := hW₁
  obtain ⟨g₂, hg₂, rfl⟩ := hW₂
  let a' : ↥(normalizer (H : Set G)) := ⟨a, ha⟩
  let w₁' : ↥(normalizer (H : Set G)) := ⟨w₁, hw₁⟩
  let w₂' : ↥(normalizer (H : Set G)) := ⟨w₂, hw₂⟩
  let g₁' : ↥(normalizer (H : Set G)) := ⟨g₁, hHn hg₁⟩
  let g₂' : ↥(normalizer (H : Set G)) := ⟨g₂, hHn hg₂⟩
  have hrel : ∀ (w : ↥(normalizer (H : Set G))) (h₁ : G), h₁ ∈ H →
      (w : G) * a * (w : G)⁻¹ = a⁻¹ * h₁ → π w * π a' * (π w)⁻¹ = (π a')⁻¹ := by
    intro w h₁ hh₁ hr
    have e : π (w * a' * w⁻¹) = π a'⁻¹ := by
      rw [hπ]
      show ((w : G) * a * (w : G)⁻¹)⁻¹ * a⁻¹ ∈ H
      rw [hr]
      have : (a⁻¹ * h₁)⁻¹ * a⁻¹ = h₁⁻¹ := by group
      rw [this]
      exact H.inv_mem hh₁
    simpa only [map_mul, map_inv] using e
  obtain ⟨h₁, hh₁, hr₁⟩ := h₁
  obtain ⟨h₂, hh₂, hr₂⟩ := h₂
  have r1 := hrel w₁' h₁ hh₁ hr₁
  have r2 := hrel w₂' h₂ hh₂ hr₂
  have hg₁1 : π g₁' = 1 := (hπ1 _).2 hg₁
  have hg₂1 : π g₂' = 1 := (hπ1 _).2 hg₂
  have key : π (w₁' * g₁' * (w₂' * g₂')) * π a' * (π (w₁' * g₁' * (w₂' * g₂')))⁻¹ = π a' := by
    simp only [map_mul, hg₁1, hg₂1, mul_one]
    have e1 : π w₁' * π w₂' * π a' * (π w₁' * π w₂')⁻¹ =
        π w₁' * (π w₂' * π a' * (π w₂')⁻¹) * (π w₁')⁻¹ := by group
    rw [e1, r2]
    have e2 : π w₁' * (π a')⁻¹ * (π w₁')⁻¹ = (π w₁' * π a' * (π w₁')⁻¹)⁻¹ := by group
    rw [e2, r1, inv_inv]
  have e : π (a' * (w₁' * g₁' * (w₂' * g₂')) * a'⁻¹) = π (w₁' * g₁' * (w₂' * g₂')) := by
    simp only [map_mul, map_inv] at key ⊢
    have hc := mul_inv_eq_iff_eq_mul.1 key
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hmem := (hπ _ _).1 e
  refine ⟨((w₁ * g₁ * (w₂ * g₂))⁻¹ * (a * (w₁ * g₁ * (w₂ * g₂)) * a⁻¹)), ?_, by group⟩
  have := H.inv_mem hmem
  have e3 : ((a * (w₁ * g₁ * (w₂ * g₂)) * a⁻¹)⁻¹ * (w₁ * g₁ * (w₂ * g₂)))⁻¹ =
      (w₁ * g₁ * (w₂ * g₂))⁻¹ * (a * (w₁ * g₁ * (w₂ * g₂)) * a⁻¹) := by group
  rw [← e3]
  exact this

end CFSG.GH74.GLS.Stage4.Rest.ZF
