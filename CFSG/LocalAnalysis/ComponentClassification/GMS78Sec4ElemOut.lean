module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4ElemDefs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Sec4Elem

variable {L T U₁ : Subgroup G} {f : ℕ}

theorem two_mul_card_lt (hE : Sec4Elem L T U₁ (2 ^ f))
    (h : Sec3 G L T) (hf : 3 ≤ f) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f))
    (hX : Sec3.Facts L T (2 ^ f)) {x : G} (hx : x ∈ U₁ ⊔ T) (hxx : x * x = 1)
    (hxW : x ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G))) {D : Subgroup G} (hDU : D ≤ U₁)
    (hDC : D ≤ centralizer ({x} : Set G)) : 2 * Nat.card D < (2 ^ f) ^ 2 := by
  by_contra hle
  push Not at hle
  have h1 := card_mul_card_le hDU hE.A_le
  rw [hE.card, (hX.sylow h).1] at h1
  have h2 : Nat.card (D ⊓ gmsA L T : Subgroup G) ≤
      Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    card_le_of_le (le_inf inf_le_right (inf_le_left.trans hDC))
  have h3 := hE.card_sq_le_of_involution h hf e hX hx hxx hxW
  have hq : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  set q := 2 ^ f
  set c := Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G)
  set d := Nat.card (D ⊓ gmsA L T : Subgroup G)
  have h4 : q ≤ 2 * d := by
    have h5 : q ^ 2 * q ≤ q ^ 2 * (2 * d) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h5 (by positivity)
  have h6 : q * q ≤ 4 * q := by nlinarith
  have := Nat.le_of_mul_le_mul_right h6 (by omega)
  omega

end Sec4Elem

end CFSG.ComponentClassification.GMS78
