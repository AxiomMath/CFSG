module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4ElemOut

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Sec4Elem

variable {L T U₁ : Subgroup G} {f : ℕ}

theorem two_mul_card_lt_V
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) {x : G}
    (hx : x ∈ U₁ ⊔ T) (hxx : x * x = 1) (hxW : x ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)))
    {D : Subgroup G} (hDV : D ≤ gmsV L T) (hDC : D ≤ centralizer ({x} : Set G)) :
    2 * Nat.card D < (2 ^ f) ^ 2 := by
  by_contra hle
  push Not at hle
  have h1 := card_mul_card_le hDV (le_sup_left : gmsA L T ≤ gmsV L T)
  rw [(hX.sylow h).1, (hX.vFacts h hF).1, hq] at h1
  have h2 : Nat.card (D ⊓ gmsA L T : Subgroup G) ≤
      Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    card_le_of_le (le_inf inf_le_right (inf_le_left.trans hDC))
  have h3 := hE.card_sq_le_of_involution h hf e hX hx hxx hxW
  have hq8 : 8 ≤ 2 ^ f := (show 8 = 2 ^ 3 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) hf
  set q := 2 ^ f
  set c := Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G)
  set d := Nat.card (D ⊓ gmsA L T : Subgroup G)
  have h4 : q ≤ 2 * d := by
    have h5 : q ^ 2 * q ≤ q ^ 2 * (2 * d) := by nlinarith
    exact Nat.le_of_mul_le_mul_left h5 (by positivity)
  have h6 : q * q ≤ 4 * q := by nlinarith
  have := Nat.le_of_mul_le_mul_right h6 (by omega)
  omega

theorem eq_or_eq_of_card
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 2 ^ f) {E : Subgroup G}
    (hES : E ≤ U₁ ⊔ T) (hEel : IsElemAbelian 2 E) (hcard : (2 ^ f) ^ 2 ≤ Nat.card E) :
    E = U₁ ∨ E = gmsV L T := by
  have hT₀ := h.isElemAbelian_T₀ hF
  have hVc : Nat.card (gmsV L T) = (2 ^ f) ^ 2 := by rw [(hX.vFacts h hF).1, hq, sq]
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hEel.2 x hx
  by_cases hEW : E ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G))
  · rcases hE.le_or_le hT₀ hEW hE2 with hU | hV
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hU (by rw [hE.card]; exact hcard))
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hV (by rw [hVc]; exact hcard))
  · exfalso
    obtain ⟨x, hxE, hxW⟩ := IsConcreteLE.not_le_iff_exists.mp hEW
    have hcard2 := hE.card_le_two_mul h hf e hES hE2
    have hDC : E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ centralizer ({x} : Set G) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (hEel.1.is_comm.comm ⟨y, (mem_inf.mp hy).1⟩ ⟨x, hxE⟩))
    rcases hE.le_or_le hT₀ (inf_le_right : E ⊓ (U₁ ⊔ (T ⊓ centralizer (L : Set G))) ≤ _)
        (fun y hy => hE2 y (mem_inf.mp hy).1) with hU | hV
    · have := hE.two_mul_card_lt h hf e hX (hES hxE) (hE2 x hxE) hxW hU hDC
      omega
    · have := hE.two_mul_card_lt_V h hF hf e hX hq (hES hxE) (hE2 x hxE) hxW hV hDC
      omega

omit [Finite G] in
theorem sup_V_eq (hE : Sec4Elem L T U₁ (2 ^ f)) :
    U₁ ⊔ gmsV L T = U₁ ⊔ (T ⊓ centralizer (L : Set G)) :=
  le_antisymm (sup_le le_sup_left hE.V_le) (sup_le_sup_left le_sup_right U₁)

end Sec4Elem

end CFSG.ComponentClassification.GMS78
