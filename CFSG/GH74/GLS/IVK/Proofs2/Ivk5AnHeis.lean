module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

structure HeisData (G : Type*) [Group G] where
  r : F4c → G
  s : F4c → G
  w : F4c → G
  r_add : ∀ a b, r (a + b) = r a * r b
  s_add : ∀ a b, s (a + b) = s a * s b
  w_add : ∀ a b, w (a + b) = w a * w b
  wr : ∀ c a, w c * r a = r a * w c
  ws : ∀ c b, w c * s b = s b * w c
  comm : ∀ a b, r a * s b = w (a * b) * (s b * r a)

theorem heis_aux {G : Type*} [Group G] (b b' a a' cx cy k : G)
    (c1 : Commute cx b') (c2 : Commute cx a') (c3 : Commute cx cy)
    (k1 : Commute k b) (k2 : Commute k b') (k3 : Commute k a) (k4 : Commute k a')
    (k5 : Commute k cx) (k6 : Commute k cy) (hc : a * b' = k * (b' * a)) :
    (b * b') * (a * a') * ((cx * cy) * k) = (b * a * cx) * (b' * a' * cy) := by
  have hcx : cx * (b' * a' * cy) = (b' * a' * cy) * cx := ((c1.mul_right c2).mul_right c3).eq
  have h1 : (b * a * cx) * (b' * a' * cy) = b * a * b' * a' * cy * cx := by
    calc (b * a * cx) * (b' * a' * cy) = b * a * (cx * (b' * a' * cy)) := by simp only [mul_assoc]
      _ = b * a * ((b' * a' * cy) * cx) := by rw [hcx]
      _ = b * a * b' * a' * cy * cx := by simp only [mul_assoc]
  have h2 : b * a * b' * a' * cy * cx = k * (b * b' * a * a' * cy * cx) := by
    calc b * a * b' * a' * cy * cx = b * (a * b') * a' * cy * cx := by simp only [mul_assoc]
      _ = b * (k * (b' * a)) * a' * cy * cx := by rw [hc]
      _ = (b * k) * (b' * a) * a' * cy * cx := by simp only [mul_assoc]
      _ = (k * b) * (b' * a) * a' * cy * cx := by rw [k1.eq.symm]
      _ = k * (b * b' * a * a' * cy * cx) := by simp only [mul_assoc]
  have hkk : (b * b' * a * a') * k = k * (b * b' * a * a') :=
    ((((k1.mul_right k2).mul_right k3).mul_right k4).eq).symm
  have hkc : (cy * cx) * k = k * (cy * cx) := ((k6.mul_right k5).eq).symm
  rw [h1, h2]
  calc (b * b') * (a * a') * ((cx * cy) * k)
      = (b * b' * a * a') * ((cy * cx) * k) := by rw [c3.eq]; simp only [mul_assoc]
    _ = (b * b' * a * a') * (k * (cy * cx)) := by rw [hkc]
    _ = ((b * b' * a * a') * k) * (cy * cx) := by simp only [mul_assoc]
    _ = (k * (b * b' * a * a')) * (cy * cx) := by rw [hkk]
    _ = k * (b * b' * a * a' * cy * cx) := by simp only [mul_assoc]

section Basis1

variable {G : Type*} [Group G] (r s w : F4c → G)

theorem comm_add_left (r_add : ∀ a b, r (a + b) = r a * r b) (wr : ∀ c a, w c * r a = r a * w c)
    (w_add : ∀ a b, w (a + b) = w a * w b) {a a' b : F4c}
    (h : r a * s b = w (a * b) * (s b * r a)) (h' : r a' * s b = w (a' * b) * (s b * r a')) :
    r (a + a') * s b = w ((a + a') * b) * (s b * r (a + a')) := by
  have hww : w (a' * b) * w (a * b) = w (a * b) * w (a' * b) := by
    rw [← w_add, ← w_add, add_comm]
  rw [r_add, add_mul, w_add]
  calc r a * r a' * s b = r a * (r a' * s b) := by simp only [mul_assoc]
    _ = r a * (w (a' * b) * (s b * r a')) := by rw [h']
    _ = (r a * w (a' * b)) * (s b * r a') := by simp only [mul_assoc]
    _ = (w (a' * b) * r a) * (s b * r a') := by rw [← wr (a' * b) a]
    _ = w (a' * b) * ((r a * s b) * r a') := by simp only [mul_assoc]
    _ = w (a' * b) * ((w (a * b) * (s b * r a)) * r a') := by rw [h]
    _ = (w (a' * b) * w (a * b)) * (s b * (r a * r a')) := by simp only [mul_assoc]
    _ = (w (a * b) * w (a' * b)) * (s b * (r a * r a')) := by rw [hww]

theorem comm_add_right (s_add : ∀ a b, s (a + b) = s a * s b) (ws : ∀ c b, w c * s b = s b * w c)
    (w_add : ∀ a b, w (a + b) = w a * w b) {a b b' : F4c}
    (h : r a * s b = w (a * b) * (s b * r a)) (h' : r a * s b' = w (a * b') * (s b' * r a)) :
    r a * s (b + b') = w (a * (b + b')) * (s (b + b') * r a) := by
  have hww : w (a * b) * w (a * b') = w (a * b') * w (a * b) := by
    rw [← w_add, ← w_add, add_comm]
  rw [s_add, mul_add, w_add]
  calc r a * (s b * s b') = (r a * s b) * s b' := by simp only [mul_assoc]
    _ = (w (a * b) * (s b * r a)) * s b' := by rw [h]
    _ = w (a * b) * (s b * (r a * s b')) := by simp only [mul_assoc]
    _ = w (a * b) * (s b * (w (a * b') * (s b' * r a))) := by rw [h']
    _ = w (a * b) * ((s b * w (a * b')) * (s b' * r a)) := by simp only [mul_assoc]
    _ = w (a * b) * ((w (a * b') * s b) * (s b' * r a)) := by rw [← ws (a * b') b]
    _ = (w (a * b) * w (a * b')) * ((s b * s b') * r a) := by simp only [mul_assoc]

end Basis1

@[expose] def omegaC : F4c := ⟨0, 1⟩

theorem F4c_cases (a : F4c) : a = 0 ∨ a = 1 ∨ a = omegaC ∨ a = 1 + omegaC := by
  revert a
  decide

theorem F4c_mul_cases : (omegaC * omegaC : F4c) = 1 + omegaC := by decide

section Basis2

variable {G : Type*} [Group G] (r s w : F4c → G)

theorem comm_of_basis (r_add : ∀ a b, r (a + b) = r a * r b) (s_add : ∀ a b, s (a + b) = s a * s b)
    (w_add : ∀ a b, w (a + b) = w a * w b) (wr : ∀ c a, w c * r a = r a * w c)
    (ws : ∀ c b, w c * s b = s b * w c)
    (h11 : r 1 * s 1 = w (1 * 1) * (s 1 * r 1))
    (h1w : r 1 * s omegaC = w (1 * omegaC) * (s omegaC * r 1))
    (hw1 : r omegaC * s 1 = w (omegaC * 1) * (s 1 * r omegaC))
    (hww : r omegaC * s omegaC = w (omegaC * omegaC) * (s omegaC * r omegaC)) :
    ∀ a b, r a * s b = w (a * b) * (s b * r a) := by
  have r0 : r 0 = 1 := by
    have h := r_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have s0 : s 0 = 1 := by
    have h := s_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have w0 : w 0 = 1 := by
    have h := w_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hb0 : ∀ a, r a * s 0 = w (a * 0) * (s 0 * r a) := by
    intro a
    rw [mul_zero, s0, w0]
    simp
  have ha0 : ∀ b, r 0 * s b = w (0 * b) * (s b * r 0) := by
    intro b
    rw [zero_mul, r0, w0]
    simp
  have hA : ∀ b, (r 1 * s b = w (1 * b) * (s b * r 1)) → (r omegaC * s b = w (omegaC * b) * (s b * r omegaC)) →
      r (1 + omegaC) * s b = w ((1 + omegaC) * b) * (s b * r (1 + omegaC)) :=
    fun b h h' => comm_add_left r s w r_add wr w_add h h'
  have hB : ∀ a, (r a * s 1 = w (a * 1) * (s 1 * r a)) → (r a * s omegaC = w (a * omegaC) * (s omegaC * r a)) →
      r a * s (1 + omegaC) = w (a * (1 + omegaC)) * (s (1 + omegaC) * r a) :=
    fun a h h' => comm_add_right r s w s_add ws w_add h h'
  have hPa : ∀ a : F4c, (r a * s 1 = w (a * 1) * (s 1 * r a)) ∧
      (r a * s omegaC = w (a * omegaC) * (s omegaC * r a)) := by
    intro a
    rcases F4c_cases a with rfl | rfl | rfl | rfl
    · exact ⟨ha0 1, ha0 omegaC⟩
    · exact ⟨h11, h1w⟩
    · exact ⟨hw1, hww⟩
    · exact ⟨hA 1 h11 hw1, hA omegaC h1w hww⟩
  intro a b
  rcases F4c_cases b with rfl | rfl | rfl | rfl
  · exact hb0 a
  · exact (hPa a).1
  · exact (hPa a).2
  · exact hB a (hPa a).1 (hPa a).2

end Basis2

namespace HeisData

variable {G : Type*} [Group G] (D : HeisData G)

theorem r_zero : D.r 0 = 1 := by
  have h := D.r_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem s_zero : D.s 0 = 1 := by
  have h := D.s_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem w_zero : D.w 0 = 1 := by
  have h := D.w_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

theorem w_comm (c c' : F4c) : D.w c * D.w c' = D.w c' * D.w c := by
  rw [← D.w_add, ← D.w_add, add_comm]

@[expose] def hom : UT3 F4c →* G where
  toFun x := D.s x.b * D.r x.a * D.w x.c
  map_one' := by
    show D.s (0 : F4c) * D.r (0 : F4c) * D.w (0 : F4c) = 1
    rw [D.r_zero, D.s_zero, D.w_zero]
    simp
  map_mul' x y := by
    show D.s (x.b + y.b) * D.r (x.a + y.a) * D.w (x.c + y.c + x.a * y.b) =
      (D.s x.b * D.r x.a * D.w x.c) * (D.s y.b * D.r y.a * D.w y.c)
    rw [D.s_add, D.r_add, D.w_add, D.w_add]
    exact heis_aux _ _ _ _ _ _ _ (D.ws _ _) (D.wr _ _) (D.w_comm _ _) (D.ws _ _) (D.ws _ _) (D.wr _ _)
      (D.wr _ _) (D.w_comm _ _) (D.w_comm _ _) (D.comm _ _)

end HeisData

@[expose] def HeisData.ofBasis {G : Type*} [Group G] (r s w : F4c → G) (r_add : ∀ a b, r (a + b) = r a * r b)
    (s_add : ∀ a b, s (a + b) = s a * s b) (w_add : ∀ a b, w (a + b) = w a * w b)
    (wr : ∀ c a, w c * r a = r a * w c) (ws : ∀ c b, w c * s b = s b * w c)
    (h11 : r 1 * s 1 = w (1 * 1) * (s 1 * r 1))
    (h1w : r 1 * s omegaC = w (1 * omegaC) * (s omegaC * r 1))
    (hw1 : r omegaC * s 1 = w (omegaC * 1) * (s 1 * r omegaC))
    (hww : r omegaC * s omegaC = w (omegaC * omegaC) * (s omegaC * r omegaC)) : HeisData G where
  r := r
  s := s
  w := w
  r_add := r_add
  s_add := s_add
  w_add := w_add
  wr := wr
  ws := ws
  comm := comm_of_basis r s w r_add s_add w_add wr ws h11 h1w hw1 hww

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
