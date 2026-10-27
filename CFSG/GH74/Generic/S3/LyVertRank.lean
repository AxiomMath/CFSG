module

public import CFSG.GH74.Generic.S3.Rank5Inv

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Filter.ClassicalOdd Subgroup
open scoped MatrixGroups

variable {F F' : Type} [Field F] [Field F'] {G : Type} [Group G]

theorem not_gen4_of_sl2_pair_inv₂ [Finite G] [Finite F] [Finite F'] (hF : ringChar F ≠ 2)
    (hF' : ringChar F' ≠ 2) {Y0 Y2 : Subgroup G} (e0 : SL(2, F) ≃* Y0) (e2 : SL(2, F') ≃* Y2)
    (hcomm : ∀ a ∈ Y0, ∀ b ∈ Y2, a * b = b * a) {w : G} (hw0 : ∀ a ∈ Y0, a * w = w * a)
    (hw2 : ∀ b ∈ Y2, b * w = w * b) (hww : w * w = 1) (hind : ∀ a ∈ Y0, ∀ b ∈ Y2, w ≠ a * b) :
    ¬ Gen4 G := by
  obtain ⟨Q⟩ := exists_quatRep hF
  obtain ⟨Q'⟩ := exists_quatRep hF'
  have hw2' : w ^ 2 = 1 := by rw [pow_two]; exact hww
  have h02 : ∀ a b, Commute (pairHom Q e0 a) (pairHom Q' e2 b) := fun a b =>
    hcomm _ (pairHom_mem Q e0 a) _ (pairHom_mem Q' e2 b)
  have hw0' : ∀ a, Commute (pairHom Q e0 a) w := fun a => hw0 _ (pairHom_mem Q e0 a)
  have hw2'' : ∀ b, Commute (pairHom Q' e2 b) w := fun b => hw2 _ (pairHom_mem Q' e2 b)
  let β : (Q8 × Q8) × Multiplicative (ZMod 2) →* (V4 × V4) × Multiplicative (ZMod 2) :=
    (q8Frattini.prodMap q8Frattini).prodMap (MonoidHom.id _)
  have hβ : Function.Surjective β :=
    (q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap Function.surjective_id
  intro hG
  refine not_sectionalTwoRankLE_of_surjection 4
    (rk5HomInv (pairHom Q e0) (pairHom Q' e2) w hw2' h02 hw0' hw2'') β hβ
    (fun a b => mul_comm a b) (by decide) (by rw [card_V4_sq_V2]; norm_num) ?_ hG
  rintro ⟨⟨a, b⟩, k⟩ hk
  rw [MonoidHom.mem_ker, rk5HomInv_apply] at hk
  rw [MonoidHom.mem_ker]
  have hn2 : (Multiplicative.toAdd k).val < 2 := ZMod.val_lt _
  set n := (Multiplicative.toAdd k).val with hn
  by_cases hev : n = 0
  · rw [hev, pow_zero, mul_one] at hk
    have hfa : q8Frattini a = 1 := by
      refine q8Frattini_of_pairHom Q e0 hcomm a ?_
      have h1 : pairHom Q e0 a = (pairHom Q' e2 b)⁻¹ := eq_inv_of_mul_eq_one_left hk
      rw [h1]
      exact inv_mem (pairHom_mem Q' e2 b)
    have hfb : q8Frattini b = 1 := by
      refine q8Frattini_of_pairHom Q' e2 (fun x hx y hy => (hcomm y hy x hx).symm) b ?_
      have h1 : pairHom Q' e2 b = (pairHom Q e0 a)⁻¹ := eq_inv_of_mul_eq_one_right hk
      rw [h1]
      exact inv_mem (pairHom_mem Q e0 a)
    have hk0 : k = 1 := toAdd_eq_zero.1 ((ZMod.val_eq_zero _).1 hev)
    exact Prod.ext (Prod.ext hfa hfb) hk0
  · exfalso
    have hn1 : n = 1 := by omega
    rw [hn1, pow_one] at hk
    have hprod : w = (pairHom Q e0 a)⁻¹ * (pairHom Q' e2 b)⁻¹ := by
      have h1 : w = (pairHom Q e0 a * pairHom Q' e2 b)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        exact hk
      rw [h1, _root_.mul_inv_rev]
      exact ((h02 a b).inv_inv).eq.symm
    exact hind _ (inv_mem (pairHom_mem Q e0 a)) _ (inv_mem (pairHom_mem Q' e2 b)) hprod

end CFSG.GH74.Generic.S3
