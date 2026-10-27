module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Exponent

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace FourGroup

variable {H : Type*} [Group H] {x y : H}

@[expose] def kleinFourOf (x y : H) (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) :
    Subgroup H where
  carrier := {1, x, y, x * y}
  one_mem' := Set.mem_insert _ _
  mul_mem' := by
    have h1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
    have h2 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
    have h3 : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
    have h4 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
    have h5 : x * y * (x * y) = 1 := by rw [← mul_assoc, h3, hy]
    have h6 : y * x = x * y := hxy.symm
    rintro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp [hx, hy, h1, h2, h3, h4, h5, h6]
  inv_mem' := by
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    have hxyi : (x * y)⁻¹ = x * y := by rw [mul_inv_rev, hxi, hyi, hxy]
    rintro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> simp [hxi, hyi, hxyi]

variable {hx : x * x = 1} {hy : y * y = 1} {hxy : x * y = y * x}

theorem mem_kleinFourOf {v : H} :
    v ∈ kleinFourOf x y hx hy hxy ↔ v = 1 ∨ v = x ∨ v = y ∨ v = x * y :=
  Iff.rfl

theorem left_mem_kleinFourOf : x ∈ kleinFourOf x y hx hy hxy :=
  Or.inr (Or.inl rfl)

theorem right_mem_kleinFourOf : y ∈ kleinFourOf x y hx hy hxy :=
  Or.inr (Or.inr (Or.inl rfl))

theorem kleinFourOf_le {K : Subgroup H} (hxK : x ∈ K) (hyK : y ∈ K) :
    kleinFourOf x y hx hy hxy ≤ K := by
  intro v hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact K.one_mem
  · exact hxK
  · exact hyK
  · exact K.mul_mem hxK hyK

theorem isElementaryAbelian_kleinFourOf :
    CFSG.IsElementaryAbelian 2 (kleinFourOf x y hx hy hxy) := by
  have hcomm : ∀ a ∈ kleinFourOf x y hx hy hxy, ∀ b ∈ kleinFourOf x y hx hy hxy,
      a * b = b * a := by
    rintro a (rfl | rfl | rfl | rfl) b (rfl | rfl | rfl | rfl) <;>
      simp only [one_mul, mul_one, mul_assoc, hxy] <;>
      simp only [← mul_assoc, hxy]
  have hsq : ∀ a ∈ kleinFourOf x y hx hy hxy, a ^ 2 = 1 := by
    rintro a (rfl | rfl | rfl | rfl)
    · exact one_pow 2
    · rw [sq, hx]
    · rw [sq, hy]
    · rw [sq, show x * y * (x * y) = x * x * (y * y) by
        rw [mul_assoc, ← mul_assoc y, ← hxy, mul_assoc, mul_assoc], hx, hy, one_mul]
  exact { is_comm := ⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
            Subtype.ext (by rw [Subgroup.coe_pow, hsq a a.2, Subgroup.coe_one]) }

theorem card_kleinFourOf (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card (kleinFourOf x y hx hy hxy) = 4 := by
  classical
  have hxy1 : x * y ≠ 1 := fun h => hne (by
    rw [← mul_one x, ← h, ← mul_assoc, hx, one_mul])
  have hxyx : x * y ≠ x := fun h => hy1 (by
    rw [← one_mul y, ← hx, mul_assoc, h, hx])
  have hxyy : x * y ≠ y := fun h => hx1 (by
    rw [← mul_one x, ← hy, ← mul_assoc, h, hy])
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  change ({1, x, y, x * y} : Set H).ncard = 4
  rw [Set.ncard_insert_of_notMem (by simp [hx1.symm, hy1.symm, hxy1.symm]),
    Set.ncard_insert_of_notMem (by simp [hne, hxyx.symm]),
    Set.ncard_insert_of_notMem (by simp [hxyy.symm]), Set.ncard_singleton]

theorem exists_kleinFour (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hne : x ≠ y) :
    ∃ V : Subgroup H, (∀ v ∈ V, v = 1 ∨ v = x ∨ v = y ∨ v = x * y) ∧
      (∀ K : Subgroup H, x ∈ K → y ∈ K → V ≤ K) ∧ CFSG.IsElementaryAbelian 2 V ∧
      Nat.card V = 4 :=
  ⟨kleinFourOf x y hx hy hxy, fun _ hv => hv, fun _ hxK hyK => kleinFourOf_le hxK hyK,
    isElementaryAbelian_kleinFourOf, card_kleinFourOf hx1 hy1 hne⟩

end FourGroup

end CFSG.LocalAnalysis.ComponentInitial
