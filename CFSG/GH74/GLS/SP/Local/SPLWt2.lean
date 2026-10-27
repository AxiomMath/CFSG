module

public import CFSG.GH74.GLS.SP.Local.SPLWt1
public import CFSG.Walter.W67.W2Cor32A
public import CFSG.GH74.GLS.SP.Local.SPLAbel

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure SPLR₁ (D : SPLNot3 G) : Prop where
  comm : ∀ a ∈ D.R₁, ∀ b ∈ D.R₁, a * b = b * a
  card : Nat.card ↥D.R₁ = D.q ^ 3
  normal : ∀ x ∈ D.P, ∀ r ∈ D.R₁, x * r * x⁻¹ ∈ D.R₁

theorem SPL3M1.toR₁ {D : SPLNot4 G} (h : SPL3M1 D) : SPLR₁ D.toSPLNot3 where
  comm := h.R₁_eab.1
  card := h.R₁_card
  normal := fun x hx r hr => by
    have hxM : x ∈ D.M₁ := (le_sup_right.trans (le_sup_left : D.B ≤ D.M₁)) hx
    exact (mem_normalizer_iff.mp (h.R₁_normal hxM) r).mp hr

section Struct

variable [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem X₂_card (h3 : SPL3M2 D) : Nat.card ↥D.X₂ = D.q := by
  show Nat.card ↥(conjBy D.t D.X₁) = D.q
  rw [card_conjBy]; exact h3.X₁_card

omit [Finite G] in
theorem X₃_card (h3 : SPL3M2 D) : Nat.card ↥D.X₃ = D.q := by
  show Nat.card ↥(conjBy D.a D.Y₁) = D.q
  rw [card_conjBy]; exact h3.Y₁_card

omit [Finite G] in
theorem X₄_card (h3 : SPL3M2 D) : Nat.card ↥D.X₄ = D.q := by
  show Nat.card ↥(conjBy D.w₁ D.X₃) = D.q
  rw [card_conjBy]; exact X₃_card D h3

omit [Finite G] in
theorem X₂_eab (h3 : SPL3M2 D) : IsEAb D.p D.X₂ := isEAb_conjBy h3.X₁_eab D.t

omit [Finite G] in
theorem X₃_eab (h3 : SPL3M2 D) : IsEAb D.p D.X₃ := isEAb_conjBy h3.Y₁_eab D.a

omit [Finite G] in
theorem X₄_eab (h3 : SPL3M2 D) : IsEAb D.p D.X₄ := isEAb_conjBy (X₃_eab D h3) D.w₁

omit [Finite G] in
theorem SPLNot3.X₁_le_R₁ : D.X₁ ≤ D.R₁ := le_sup_left.trans le_sup_left
omit [Finite G] in
theorem SPLNot3.X₂_le_R₁ : D.X₂ ≤ D.R₁ := le_sup_right.trans le_sup_left
omit [Finite G] in
theorem SPLNot3.X₃_le_R₁ : D.X₃ ≤ D.R₁ := le_sup_right
omit [Finite G] in
theorem SPLNot3.R₁_le_P : D.R₁ ≤ D.P := by
  show D.X₁ ⊔ D.X₂ ⊔ D.X₃ ≤ D.X₁ ⊔ (D.X₂ ⊔ D.X₃ ⊔ D.X₄)
  refine sup_le (sup_le le_sup_left ?_) ?_
  · exact le_sup_left.trans (le_sup_left.trans le_sup_right)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_right)
omit [Finite G] in
theorem SPLNot3.X₄_le_P : D.X₄ ≤ D.P := le_sup_right.trans le_sup_right
omit [Finite G] in
theorem SPLNot3.P_eq_R₁_sup_X₄ : D.P = D.R₁ ⊔ D.X₄ := by
  show D.X₁ ⊔ (D.X₂ ⊔ D.X₃ ⊔ D.X₄) = D.X₁ ⊔ D.X₂ ⊔ D.X₃ ⊔ D.X₄
  simp only [sup_assoc]

theorem R₁_decomp (h3 : SPL3M2 D) (hR : SPLR₁ D) :
    (∀ r ∈ D.R₁, ∃ x₁ ∈ D.X₁, ∃ x₂ ∈ D.X₂, ∃ x₃ ∈ D.X₃, r = x₁ * x₂ * x₃) ∧
    (∀ x₁ ∈ D.X₁, ∀ x₂ ∈ D.X₂, ∀ x₃ ∈ D.X₃, x₁ * x₂ * x₃ = 1 → x₁ = 1 ∧ x₂ = 1 ∧ x₃ = 1) :=
  direct_of_card D.R₁ D.X₁ D.X₂ D.X₃ hR.comm D.X₁_le_R₁ D.X₂_le_R₁ D.X₃_le_R₁ le_rfl
    (by rw [hR.card, h3.X₁_card, X₂_card D h3, X₃_card D h3]; ring)

theorem X₂_inf_X₃ (h3 : SPL3M2 D) (hR : SPLR₁ D) : D.X₂ ⊓ D.X₃ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨h2, h3'⟩
  have := (R₁_decomp D h3 hR).2 1 (Subgroup.one_mem _) x h2 x⁻¹ (Subgroup.inv_mem _ h3')
    (by group)
  exact this.2.1

theorem X₄_inf_R₁ (h3 : SPL3M2 D) (hR : SPLR₁ D) : D.X₄ ⊓ D.R₁ = ⊥ := by
  have hP : Nat.card ↥(D.R₁ ⊔ D.X₄ : Subgroup G) = D.q ^ 4 := by
    rw [← D.P_eq_R₁_sup_X₄]; exact h3.P_card
  have hnorm : D.X₄ ≤ normalizer (D.R₁ : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro r
    constructor
    · intro hr; exact hR.normal x (D.X₄_le_P hx) r hr
    · intro hr
      have := hR.normal x⁻¹ (Subgroup.inv_mem _ (D.X₄_le_P hx)) _ hr
      simpa [mul_assoc] using this
  have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer (A := D.R₁) (B := D.X₄) hnorm
  rw [hP, hR.card, X₄_card D h3] at h
  have hq : 0 < D.q ^ 4 := by
    have := h3.X₁_card ▸ (Nat.card_pos : 0 < Nat.card ↥D.X₁)
    exact Nat.pow_pos this
  have h1 : Nat.card ↥(D.R₁ ⊓ D.X₄) = 1 := by
    have : D.q ^ 4 * Nat.card ↥(D.R₁ ⊓ D.X₄) = D.q ^ 4 * 1 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hq this
  rw [inf_comm]
  exact (Subgroup.card_eq_one).mp h1

end Struct

end CFSG.GH74.GLS.SP.Local
