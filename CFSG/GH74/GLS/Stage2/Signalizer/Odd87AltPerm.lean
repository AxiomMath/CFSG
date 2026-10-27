module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltPerm

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α]

@[expose] def c3 (a b e : α) : Perm α := swap a b * swap b e

structure Trip (y : Perm α) (a b e : α) : Prop where
  ha : y a ≠ a
  hb : y b ≠ b
  he : y e ≠ e
  hba : b ≠ a
  hbya : b ≠ y a
  hea : e ≠ a
  heya : e ≠ y a
  heb : e ≠ b
  heyb : e ≠ y b

structure Six (y : Perm α) (a b e : α) : Prop where
  a_ya : a ≠ y a
  a_b : a ≠ b
  a_yb : a ≠ y b
  a_e : a ≠ e
  a_ye : a ≠ y e
  ya_b : y a ≠ b
  ya_yb : y a ≠ y b
  ya_e : y a ≠ e
  ya_ye : y a ≠ y e
  b_yb : b ≠ y b
  b_e : b ≠ e
  b_ye : b ≠ y e
  yb_e : y b ≠ e
  yb_ye : y b ≠ y e
  e_ye : e ≠ y e

@[expose] def V (y : Perm α) (a b e : α) : Perm α := c3 a b e * c3 (y a) (y b) (y e)

@[expose] def U (y : Perm α) (a b : α) : Perm α := swap a (y a) * swap b (y b)

omit [DecidableEq α] in
theorem yy {y : Perm α} (hy : y * y = 1) (x : α) : y (y x) = x := by
  have := congrArg (fun f : Perm α => f x) hy
  simpa using this

omit [DecidableEq α] in
theorem y_eq_symm {y : Perm α} (hy : y * y = 1) {u v : α} (h : y u = v) : y v = u := by
  rw [← h]; exact yy hy u

omit [DecidableEq α] in
theorem y_inj {y : Perm α} (hy : y * y = 1) {u v : α} (h : y u = y v) : u = v := by
  have := congrArg y h
  rwa [yy hy, yy hy] at this

omit [DecidableEq α] in
theorem Trip.six {y : Perm α} {a b e : α} (hy : y * y = 1) (h : Trip y a b e) : Six y a b e where
  a_ya := fun h' => h.ha h'.symm
  a_b := fun h' => h.hba h'.symm
  a_yb := fun h' => h.hbya (y_eq_symm hy h'.symm).symm
  a_e := fun h' => h.hea h'.symm
  a_ye := fun h' => h.heya (y_eq_symm hy h'.symm).symm
  ya_b := fun h' => h.hbya h'.symm
  ya_yb := fun h' => h.hba (y_inj hy h').symm
  ya_e := fun h' => h.heya h'.symm
  ya_ye := fun h' => h.hea (y_inj hy h').symm
  b_yb := fun h' => h.hb h'.symm
  b_e := fun h' => h.heb h'.symm
  b_ye := fun h' => h.heyb (y_eq_symm hy h'.symm).symm
  yb_e := fun h' => h.heyb h'.symm
  yb_ye := fun h' => h.heb (y_inj hy h').symm
  e_ye := fun h' => h.he h'.symm

omit [DecidableEq α] in
theorem Trip.rot {y : Perm α} {a b e : α} (hy : y * y = 1) (h : Trip y a b e) : Trip y b e a := by
  have S := h.six hy
  exact ⟨h.hb, h.he, h.ha, h.heb, h.heyb, S.a_b, S.a_yb, S.a_e, S.a_ye⟩

omit [DecidableEq α] in
theorem Trip.swap23 {y : Perm α} {a b e : α} (hy : y * y = 1) (h : Trip y a b e) :
    Trip y a e b := by
  have S := h.six hy
  exact ⟨h.ha, h.he, h.hb, h.hea, h.heya, h.hba, h.hbya, h.heb.symm, S.b_ye⟩

section Cycle

theorem c3_apply_left {a b e : α} (hab : a ≠ b) (hae : a ≠ e) : c3 a b e a = b := by
  rw [c3, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hae, Equiv.swap_apply_left]

theorem c3_apply_of_ne {a b e w : α} (hwa : w ≠ a) (hwb : w ≠ b) (hwe : w ≠ e) : c3 a b e w = w := by
  rw [c3, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwb hwe, Equiv.swap_apply_of_ne_of_ne hwa hwb]

theorem c3_pow_three [Fintype α] {a b e : α} (hab : a ≠ b) (hbe : b ≠ e) (hae : a ≠ e) :
    c3 a b e ^ 3 = 1 := by
  have h3 : (c3 a b e).IsThreeCycle := by
    have := Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := b) (b := a) (c := e) hab.symm hbe hae
    rwa [c3, Equiv.swap_comm]
  have := Equiv.Perm.IsThreeCycle.orderOf h3
  rw [← this]
  exact pow_orderOf_eq_one _

theorem conj_c3 (f : Perm α) (a b e : α) : f * c3 a b e * f⁻¹ = c3 (f a) (f b) (f e) := by
  rw [c3, c3, Equiv.swap_apply_apply, Equiv.swap_apply_apply]
  group

theorem c3_mul_comm_of_fixed {y : Perm α} {a b e : α} (ha : y a = a) (hb : y b = b) (he : y e = e) :
    c3 a b e * y = y * c3 a b e := by
  have h := conj_c3 y a b e
  rw [ha, hb, he] at h
  calc c3 a b e * y = (y * c3 a b e * y⁻¹) * y := by rw [h]
    _ = y * c3 a b e := by group

end Cycle

section VLemmas

variable {y : Perm α} {a b e : α}

theorem V_apply_left (hy : y * y = 1) (h : Trip y a b e) : V y a b e a = b := by
  have S := h.six hy
  rw [V, Perm.mul_apply, c3_apply_of_ne S.a_ya S.a_yb S.a_ye, c3_apply_left S.a_b S.a_e]

theorem V_apply_left' (hy : y * y = 1) (h : Trip y a b e) : V y a b e (y a) = y b := by
  have S := h.six hy
  rw [V, Perm.mul_apply, c3_apply_left S.ya_yb S.ya_ye,
    c3_apply_of_ne S.a_yb.symm S.b_yb.symm S.yb_e]

theorem V_apply_of_ne {w : α}
    (hwa : w ≠ a) (hwya : w ≠ y a) (hwb : w ≠ b) (hwyb : w ≠ y b) (hwe : w ≠ e) (hwye : w ≠ y e) :
    V y a b e w = w := by
  rw [V, Perm.mul_apply, c3_apply_of_ne hwya hwyb hwye, c3_apply_of_ne hwa hwb hwe]

theorem V_commute (hy : y * y = 1) (h : Trip y a b e) :
    Commute (c3 a b e) (c3 (y a) (y b) (y e)) := by
  have S := h.six hy
  refine Equiv.Perm.Disjoint.commute ?_
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  intro w
  by_cases hwa : w = a
  · right; rw [hwa]; exact c3_apply_of_ne S.a_ya S.a_yb S.a_ye
  by_cases hwb : w = b
  · right; rw [hwb]; exact c3_apply_of_ne S.ya_b.symm S.b_yb S.b_ye
  by_cases hwe : w = e
  · right; rw [hwe]; exact c3_apply_of_ne S.ya_e.symm S.yb_e.symm S.e_ye
  · left; exact c3_apply_of_ne hwa hwb hwe

theorem V_mul_comm (hy : y * y = 1) (h : Trip y a b e) : V y a b e * y = y * V y a b e := by
  have hc := V_commute hy h
  have hyP : y * c3 a b e * y⁻¹ = c3 (y a) (y b) (y e) := conj_c3 y a b e
  have hyQ : y * c3 (y a) (y b) (y e) * y⁻¹ = c3 a b e := by
    rw [conj_c3, yy hy, yy hy, yy hy]
  have : y * (c3 a b e * c3 (y a) (y b) (y e)) = (c3 a b e * c3 (y a) (y b) (y e)) * y := by
    calc y * (c3 a b e * c3 (y a) (y b) (y e))
        = (y * c3 a b e * y⁻¹) * (y * c3 (y a) (y b) (y e) * y⁻¹) * y := by group
      _ = c3 (y a) (y b) (y e) * c3 a b e * y := by rw [hyP, hyQ]
      _ = (c3 a b e * c3 (y a) (y b) (y e)) * y := by rw [hc.eq]
  exact this.symm

theorem V_pow_three [Fintype α] (hy : y * y = 1) (h : Trip y a b e) : V y a b e ^ 3 = 1 := by
  have S := h.six hy
  have hc := V_commute hy h
  rw [V, hc.mul_pow, c3_pow_three S.a_b S.b_e S.a_e,
    c3_pow_three S.ya_yb S.yb_ye S.ya_ye, one_mul]

end VLemmas

section ULemmas

variable {y : Perm α} {a b e : α}

theorem swap_mul_comm (hy : y * y = 1) : swap a (y a) * y = y * swap a (y a) := by
  have h1 := Equiv.swap_apply_apply y a (y a)
  rw [yy hy, Equiv.swap_comm] at h1
  calc swap a (y a) * y = (y * swap a (y a) * y⁻¹) * y := by rw [← h1]
    _ = y * swap a (y a) := by group

theorem U_apply_left (hy : y * y = 1) (h : Trip y a b e) : U y a b a = y a := by
  have S := h.six hy
  rw [U, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne S.a_b S.a_yb, Equiv.swap_apply_left]

theorem U_apply_left' (hy : y * y = 1) (h : Trip y a b e) : U y a b (y a) = a := by
  have S := h.six hy
  rw [U, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne S.ya_b S.ya_yb, Equiv.swap_apply_right]

theorem U_apply_right (hy : y * y = 1) (h : Trip y a b e) : U y a b b = y b := by
  have S := h.six hy
  rw [U, Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne S.a_yb.symm S.ya_yb.symm]

theorem U_apply_right' (hy : y * y = 1) (h : Trip y a b e) : U y a b (y b) = b := by
  have S := h.six hy
  rw [U, Perm.mul_apply, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne S.a_b.symm S.ya_b.symm]

theorem U_apply_of_ne {w : α} (hwa : w ≠ a) (hwya : w ≠ y a) (hwb : w ≠ b) (hwyb : w ≠ y b) :
    U y a b w = w := by
  rw [U, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwb hwyb,
    Equiv.swap_apply_of_ne_of_ne hwa hwya]

theorem U_mul_self (hy : y * y = 1) (h : Trip y a b e) : U y a b * U y a b = 1 := by
  have S := h.six hy
  ext w
  rw [Perm.mul_apply, Perm.one_apply]
  by_cases h1 : w = a
  · rw [h1, U_apply_left hy h, U_apply_left' hy h]
  by_cases h2 : w = y a
  · rw [h2, U_apply_left' hy h, U_apply_left hy h]
  by_cases h3 : w = b
  · rw [h3, U_apply_right hy h, U_apply_right' hy h]
  by_cases h4 : w = y b
  · rw [h4, U_apply_right' hy h, U_apply_right hy h]
  · rw [U_apply_of_ne h1 h2 h3 h4, U_apply_of_ne h1 h2 h3 h4]

theorem U_eq_comm (hy : y * y = 1) (h : Trip y a b e) :
    U y a b = (swap a (y a) * V y a b e * (swap a (y a))⁻¹) * (V y a b e)⁻¹ := by
  have h1 := Equiv.swap_apply_apply (V y a b e) a (y a)
  rw [V_apply_left hy h, V_apply_left' hy h] at h1
  calc U y a b = swap a (y a) * swap b (y b) := rfl
    _ = swap a (y a) * (V y a b e * swap a (y a) * (V y a b e)⁻¹) := by rw [← h1]
    _ = (swap a (y a) * V y a b e * (swap a (y a))⁻¹) * (V y a b e)⁻¹ := by
      rw [Equiv.swap_inv]; group

end ULemmas

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltPerm
