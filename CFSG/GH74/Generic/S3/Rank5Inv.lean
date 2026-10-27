module

public import CFSG.GH74.Generic.S3.Rank5

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.Filter.ClassicalOdd Subgroup
open scoped MatrixGroups

variable {F : Type} [Field F] {G : Type} [Group G]

@[expose] def zPow2 (w : G) (hw : w ^ 2 = 1) : Multiplicative (ZMod 2) →* G where
  toFun k := w ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hw, pow_add]

theorem zPow2_apply (w : G) (hw : w ^ 2 = 1) (k : Multiplicative (ZMod 2)) :
    zPow2 w hw k = w ^ (Multiplicative.toAdd k).val := rfl

@[expose] def rk5HomInv (φ0 φ2 : Q8 →* G) (w : G) (hw : w ^ 2 = 1)
    (h02 : ∀ a b, Commute (φ0 a) (φ2 b)) (hw0 : ∀ a, Commute (φ0 a) w)
    (hw2 : ∀ b, Commute (φ2 b) w) : (Q8 × Q8) × Multiplicative (ZMod 2) →* G :=
  MonoidHom.noncommCoprod (MonoidHom.noncommCoprod φ0 φ2 h02) (zPow2 w hw) (fun ab k => by
    rw [MonoidHom.noncommCoprod_apply, zPow2_apply]
    exact ((hw0 ab.1).mul_left (hw2 ab.2)).pow_right _)

theorem rk5HomInv_apply (φ0 φ2 : Q8 →* G) (w : G) (hw : w ^ 2 = 1)
    (h02 : ∀ a b, Commute (φ0 a) (φ2 b)) (hw0 : ∀ a, Commute (φ0 a) w)
    (hw2 : ∀ b, Commute (φ2 b) w) (a b : Q8) (k : Multiplicative (ZMod 2)) :
    rk5HomInv φ0 φ2 w hw h02 hw0 hw2 ((a, b), k) = φ0 a * φ2 b * w ^ (Multiplicative.toAdd k).val :=
  rfl

theorem not_gen4_of_sl2_pair_inv [Finite G] [Finite F] (hF : ringChar F ≠ 2)
    {Y0 Y2 : Subgroup G} (e0 : SL(2, F) ≃* Y0) (e2 : SL(2, F) ≃* Y2)
    (hcomm : ∀ a ∈ Y0, ∀ b ∈ Y2, a * b = b * a) {w : G} (hw0 : ∀ a ∈ Y0, a * w = w * a)
    (hw2 : ∀ b ∈ Y2, b * w = w * b) (hww : w * w = 1) (hind : ∀ a ∈ Y0, ∀ b ∈ Y2, w ≠ a * b) :
    ¬ Gen4 G := by
  obtain ⟨Q⟩ := exists_quatRep hF
  have hw2' : w ^ 2 = 1 := by rw [pow_two]; exact hww
  have h02 : ∀ a b, Commute (pairHom Q e0 a) (pairHom Q e2 b) := fun a b =>
    hcomm _ (pairHom_mem Q e0 a) _ (pairHom_mem Q e2 b)
  have hw0' : ∀ a, Commute (pairHom Q e0 a) w := fun a => hw0 _ (pairHom_mem Q e0 a)
  have hw2'' : ∀ b, Commute (pairHom Q e2 b) w := fun b => hw2 _ (pairHom_mem Q e2 b)
  let β : (Q8 × Q8) × Multiplicative (ZMod 2) →* (V4 × V4) × Multiplicative (ZMod 2) :=
    (q8Frattini.prodMap q8Frattini).prodMap (MonoidHom.id _)
  have hβ : Function.Surjective β :=
    (q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap Function.surjective_id
  intro hG
  refine not_sectionalTwoRankLE_of_surjection 4
    (rk5HomInv (pairHom Q e0) (pairHom Q e2) w hw2' h02 hw0' hw2'') β hβ
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
      have h1 : pairHom Q e0 a = (pairHom Q e2 b)⁻¹ := eq_inv_of_mul_eq_one_left hk
      rw [h1]
      exact inv_mem (pairHom_mem Q e2 b)
    have hfb : q8Frattini b = 1 := by
      refine q8Frattini_of_pairHom Q e2 (fun x hx y hy => (hcomm y hy x hx).symm) b ?_
      have h1 : pairHom Q e2 b = (pairHom Q e0 a)⁻¹ := eq_inv_of_mul_eq_one_right hk
      rw [h1]
      exact inv_mem (pairHom_mem Q e0 a)
    have hk0 : k = 1 := toAdd_eq_zero.1 ((ZMod.val_eq_zero _).1 hev)
    exact Prod.ext (Prod.ext hfa hfb) hk0
  · exfalso
    have hn1 : n = 1 := by omega
    rw [hn1, pow_one] at hk
    have hprod : w = (pairHom Q e0 a)⁻¹ * (pairHom Q e2 b)⁻¹ := by
      have h1 : w = (pairHom Q e0 a * pairHom Q e2 b)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        exact hk
      rw [h1, _root_.mul_inv_rev]
      exact ((h02 a b).inv_inv).eq.symm
    exact hind _ (inv_mem (pairHom_mem Q e0 a)) _ (inv_mem (pairHom_mem Q e2 b)) hprod

theorem not_gen4_of_sl2_pair_sq [Finite G] [Finite F] (hF : ringChar F ≠ 2)
    {Y0 Y2 : Subgroup G} (e0 : SL(2, F) ≃* Y0) (e2 : SL(2, F) ≃* Y2)
    (hcomm : ∀ a ∈ Y0, ∀ b ∈ Y2, a * b = b * a) {z w : G} (hz0 : z ∈ Y0) (hz2 : z ∈ Y2)
    (hzz : z * z = 1) (hw0 : ∀ a ∈ Y0, a * w = w * a) (hw2 : ∀ b ∈ Y2, b * w = w * b)
    (hww : w * w = 1 ∨ w * w = z) (hind : ∀ a ∈ Y0, ∀ b ∈ Y2, w ≠ a * b) : ¬ Gen4 G := by
  rcases hww with h | h
  · exact not_gen4_of_sl2_pair_inv hF e0 e2 hcomm hw0 hw2 h hind
  · exact not_gen4_of_sl2_pair hF e0 e2 hcomm hz0 hz2 hzz hw0 hw2 h hind

theorem mem_center_pair_of_commute (hF : ringChar F ≠ 2) {Y0 Y2 : Subgroup G}
    (e0 : SL(2, F) ≃* Y0) (e2 : SL(2, F) ≃* Y2) (hcomm : ∀ a ∈ Y0, ∀ b ∈ Y2, a * b = b * a)
    {z : G} (hz0 : z ∈ Y0) (hz2 : z ∈ Y2) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hzc0 : ∀ a ∈ Y0, a * z = z * a) (hzc2 : ∀ b ∈ Y2, b * z = z * b)
    {x : G} (hx0 : ∀ a ∈ Y0, a * x = x * a) (hx2 : ∀ b ∈ Y2, b * x = x * b)
    {a b : G} (ha : a ∈ Y0) (hb : b ∈ Y2) (hab : x = a * b) : x = 1 ∨ x = z := by
  have ha0 : ∀ c ∈ Y0, c * a = a * c := by
    intro c hc
    have h1 := hx0 c hc
    rw [hab] at h1
    have h2 : c * a * b = a * c * b := by
      calc c * a * b = c * (a * b) := by rw [mul_assoc]
        _ = (a * b) * c := h1
        _ = a * (b * c) := by rw [mul_assoc]
        _ = a * (c * b) := by rw [← hcomm c hc b hb]
        _ = a * c * b := by rw [mul_assoc]
    exact mul_right_cancel h2
  have hb2 : ∀ c ∈ Y2, c * b = b * c := by
    intro c hc
    have h1 := hx2 c hc
    rw [hab] at h1
    have h2 : a * (c * b) = a * (b * c) := by
      calc a * (c * b) = (a * c) * b := by rw [mul_assoc]
        _ = (c * a) * b := by rw [hcomm a ha c hc]
        _ = c * (a * b) := by rw [mul_assoc]
        _ = (a * b) * c := h1
        _ = a * (b * c) := by rw [mul_assoc]
    exact mul_left_cancel h2
  have hsa := (sl2_img_eq_z hF e0 hz0 hzc0 hz1).1 a ha (fun c hc => (ha0 c hc).symm)
  have hsb := (sl2_img_eq_z hF e2 hz2 hzc2 hz1).1 b hb (fun c hc => (hb2 c hc).symm)
  rw [hab]
  rcases hsa with h1 | h1 <;> rcases hsb with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; rw [h1, h2, one_mul]
  · right; rw [h1, h2, mul_one]
  · left; rw [h1, h2]; exact hzz

end CFSG.GH74.Generic.S3
