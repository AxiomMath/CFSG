module

public import Mathlib.Tactic.Group
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.ClassicalInvolution.Q3.Q3CP

variable {X : Type*} [Group X]

structure QuatPair (x y ζ : X) : Prop where
  xx : x * x = ζ
  yy : y * y = ζ
  xy : x * y = ζ * (y * x)
  zz : ζ * ζ = 1
  ne : ζ ≠ 1
  cen : ∀ g : X, g * ζ = ζ * g

namespace QuatPair

variable {x y ζ : X}

theorem yx (h : QuatPair x y ζ) : y * x = ζ * (x * y) := by
  calc y * x = (ζ * ζ) * (y * x) := by rw [h.zz, one_mul]
    _ = ζ * (ζ * (y * x)) := mul_assoc _ _ _
    _ = ζ * (x * y) := by rw [← h.xy]

theorem cen_mul (h : QuatPair x y ζ) (u v : X) : (ζ * u) * (ζ * v) = (ζ * ζ) * (u * v) := by
  calc (ζ * u) * (ζ * v) = ζ * (u * ζ) * v := by group
    _ = ζ * (ζ * u) * v := by rw [h.cen u]
    _ = (ζ * ζ) * (u * v) := by group

theorem xy_ne (h : QuatPair x y ζ) : x * y ≠ y * x := by
  intro hc
  apply h.ne
  have h1 : ζ * (y * x) = 1 * (y * x) := by rw [← h.xy, hc, one_mul]
  exact mul_right_cancel h1

end QuatPair

section Prod

variable {x y x' y' ζ : X}

theorem quatPair_prod_sq_a (h : QuatPair x y ζ) (h' : QuatPair x' y' ζ) (hxx' : x * x' = x' * x) :
    (x * x') * (x * x') = 1 := by
  calc (x * x') * (x * x') = x * (x' * x) * x' := by group
    _ = x * (x * x') * x' := by rw [← hxx']
    _ = (x * x) * (x' * x') := by group
    _ = 1 := by rw [h.xx, h'.xx, h.zz]

theorem quatPair_prod_sq_b (h : QuatPair x y ζ) (h' : QuatPair x' y' ζ) (hyy' : y * y' = y' * y) :
    (y * y') * (y * y') = 1 := by
  calc (y * y') * (y * y') = y * (y' * y) * y' := by group
    _ = y * (y * y') * y' := by rw [← hyy']
    _ = (y * y) * (y' * y') := by group
    _ = 1 := by rw [h.yy, h'.yy, h.zz]

theorem quatPair_prod_comm (h : QuatPair x y ζ) (h' : QuatPair x' y' ζ) (hxy' : x * y' = y' * x)
    (hyx' : y * x' = x' * y) :
    (x * x') * (y * y') = (y * y') * (x * x') := by
  have h1 : x' * y = y * x' := hyx'.symm
  have h2 : y' * x = x * y' := hxy'.symm
  calc (x * x') * (y * y') = x * (x' * y) * y' := by group
    _ = x * (y * x') * y' := by rw [h1]
    _ = (x * y) * (x' * y') := by group
    _ = (ζ * (y * x)) * (ζ * (y' * x')) := by rw [h.xy, h'.xy]
    _ = (ζ * ζ) * ((y * x) * (y' * x')) := h.cen_mul _ _
    _ = (y * x) * (y' * x') := by rw [h.zz, one_mul]
    _ = y * (x * y') * x' := by group
    _ = y * (y' * x) * x' := by rw [h2]
    _ = (y * y') * (x * x') := by group

theorem quatPair_prod_a_ne (h : QuatPair x y ζ) (hyx' : y * x' = x' * y) :
    (x * x') * y ≠ y * (x * x') := by
  intro hc
  have h1 : (x * x') * y = ζ * (y * (x * x')) := by
    calc (x * x') * y = x * (x' * y) := by group
      _ = x * (y * x') := by rw [← hyx']
      _ = (x * y) * x' := by group
      _ = (ζ * (y * x)) * x' := by rw [h.xy]
      _ = ζ * (y * (x * x')) := by group
  apply h.ne
  have h2 : ζ * (y * (x * x')) = 1 * (y * (x * x')) := by rw [← h1, hc, one_mul]
  exact mul_right_cancel h2

theorem quatPair_prod_b_eq (h : QuatPair x y ζ) (hxy' : x * y' = y' * x) :
    (y * y') * x = ζ * (x * (y * y')) := by
  calc (y * y') * x = y * (y' * x) := by group
    _ = y * (x * y') := by rw [← hxy']
    _ = (y * x) * y' := by group
    _ = (ζ * (x * y)) * y' := by rw [h.yx]
    _ = ζ * (x * (y * y')) := by group

theorem quatPair_prod_b_ne (h : QuatPair x y ζ) (hxy' : x * y' = y' * x) :
    (y * y') * x ≠ x * (y * y') := by
  intro hc
  have h1 := quatPair_prod_b_eq (y' := y') h hxy'
  apply h.ne
  have h2 : ζ * (x * (y * y')) = 1 * (x * (y * y')) := by rw [← h1, hc, one_mul]
  exact mul_right_cancel h2

theorem quatPair_prod_ab_ne (h : QuatPair x y ζ) (hxx' : x * x' = x' * x)
    (hxy' : x * y' = y' * x) : ((x * x') * (y * y')) * x ≠ x * ((x * x') * (y * y')) := by
  intro hc
  have hb := quatPair_prod_b_eq (y' := y') h hxy'
  have h1 : ((x * x') * (y * y')) * x = ζ * (x * ((x * x') * (y * y'))) := by
    calc ((x * x') * (y * y')) * x = (x * x') * ((y * y') * x) := by group
      _ = (x * x') * (ζ * (x * (y * y'))) := by rw [hb]
      _ = ((x * x') * ζ) * (x * (y * y')) := by group
      _ = (ζ * (x * x')) * (x * (y * y')) := by rw [h.cen (x * x')]
      _ = ζ * (((x * x') * x) * (y * y')) := by group
      _ = ζ * ((x * (x * x')) * (y * y')) := by
          rw [show (x * x') * x = x * (x * x') by
            calc (x * x') * x = x * (x' * x) := by group
              _ = x * (x * x') := by rw [← hxx']]
      _ = ζ * (x * ((x * x') * (y * y'))) := by group
  apply h.ne
  have h2 : ζ * (x * ((x * x') * (y * y'))) = 1 * (x * ((x * x') * (y * y'))) := by
    rw [← h1, hc, one_mul]
  exact mul_right_cancel h2

end Prod

end CFSG.ClassicalInvolution.Q3.Q3CP
