module

public import CFSG.ClassicalInvolution.Phan.PhanQ1Pair

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

variable {F : Type} [Field F]

theorem B8_add_left (x y z : V8 F) : B8 (x + y) z = B8 x z + B8 y z := polar_add_left _ _ _ _

theorem B8_add_right (x y z : V8 F) : B8 z (x + y) = B8 z x + B8 z y := polar_add_right _ _ _ _

theorem B8_sub_left (x y z : V8 F) : B8 (x - y) z = B8 x z - B8 y z := polar_sub_left _ _ _ _

theorem B8_sub_right (x y z : V8 F) : B8 z (x - y) = B8 z x - B8 z y := polar_sub_right _ _ _ _

theorem B8_smul_left (a : F) (x y : V8 F) : B8 (a • x) y = a * B8 x y := by
  rw [B8, polar_smul_left]
  rfl

theorem B8_smul_right (a : F) (x y : V8 F) : B8 y (a • x) = a * B8 y x := by
  rw [B8_comm, B8_smul_left, B8_comm]

theorem Q8_sub (x y : V8 F) : Q8 (x - y) = Q8 x + Q8 y - B8 x y := by
  have h : x - y = (1 : F) • x + (-1 : F) • y := by module
  rw [h, Q8_lin]
  ring

variable {ε : F}

theorem exists_split (h2 : (2 : F) ≠ 0) (hε : ε ≠ 0) {z w : NPair ε} (h : ColP ε z w) :
    ∃ (P S : F) (u v : V8 F),
      w.x = (P / 2) • z.x + (S / (2 * ε)) • z.y + u ∧
      w.y = (-(S / 2)) • z.x + (P / 2) • z.y + v ∧
      P ^ 2 + S ^ 2 / ε ≠ 4 ∧
      B8 z.x u = 0 ∧ B8 z.y u = 0 ∧ B8 z.x v = 0 ∧ B8 z.y v = 0 ∧
      Q8 u = 1 - (P ^ 2 + S ^ 2 / ε) / 4 ∧ Q8 v = ε * (1 - (P ^ 2 + S ^ 2 / ε) / 4) ∧
      B8 u v = 0 := by
  obtain ⟨h1, h2', h3⟩ := h
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  set P := B8 z.x w.x with hP
  set S := B8 z.y w.x with hS
  have hxx : B8 z.x z.x = 2 := by rw [B8_self, z.hx]; ring
  have hyy : B8 z.y z.y = 2 * ε := by rw [B8_self, z.hy]
  have hxy : B8 z.x z.y = 0 := z.hxy
  have hyx : B8 z.y z.x = 0 := by rw [B8_comm]; exact z.hxy
  have e1 : B8 z.y w.y = ε * P := h1
  have e2 : B8 z.x w.y = -S := by linear_combination h2'
  have e3 : B8 w.x z.x = P := by rw [B8_comm]
  have e4 : B8 w.x z.y = S := by rw [B8_comm]
  have e5 : B8 w.y z.x = -S := by rw [B8_comm]; exact e2
  have e6 : B8 w.y z.y = ε * P := by rw [B8_comm]; exact e1
  have hw : B8 w.x w.y = 0 := w.hxy
  refine ⟨P, S, w.x - ((P / 2) • z.x + (S / (2 * ε)) • z.y),
    w.y - ((-(S / 2)) • z.x + (P / 2) • z.y), by abel, by abel, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [B8_sub_right, B8_add_right, B8_smul_right, hxx, hxy]
    rw [← hP]
    field_simp
    ring
  · simp only [B8_sub_right, B8_add_right, B8_smul_right, hyy, hyx]
    rw [← hS]
    field_simp
    ring
  · simp only [B8_sub_right, B8_add_right, B8_smul_right, hxx, hxy, e2]
    field_simp
    ring
  · simp only [B8_sub_right, B8_add_right, B8_smul_right, hyy, hyx, e1]
    field_simp
    ring
  · rw [Q8_sub, w.hx]
    have hq : Q8 ((P / 2) • z.x + (S / (2 * ε)) • z.y) =
        (P / 2) ^ 2 + ε * (S / (2 * ε)) ^ 2 := by
      rw [Q8_lin, z.hx, z.hy, hxy]
      ring
    have hb : B8 w.x ((P / 2) • z.x + (S / (2 * ε)) • z.y) = P * P / 2 + S * S / (2 * ε) := by
      simp only [B8_add_right, B8_smul_right, e3, e4]
      ring
    rw [hq, hb]
    field_simp
    ring
  · rw [Q8_sub, w.hy]
    have hq : Q8 ((-(S / 2)) • z.x + (P / 2) • z.y) = (-(S / 2)) ^ 2 + ε * (P / 2) ^ 2 := by
      rw [Q8_lin, z.hx, z.hy, hxy]
      ring
    have hb : B8 w.y ((-(S / 2)) • z.x + (P / 2) • z.y) = S * S / 2 + ε * P * P / 2 := by
      simp only [B8_add_right, B8_smul_right, e5, e6]
      ring
    rw [hq, hb]
    field_simp
    ring
  · simp only [B8_sub_right, B8_sub_left, B8_add_right, B8_add_left, B8_smul_right, B8_smul_left,
      hw, e2, e1, e3, e4, hxx, hxy, hyx, hyy]
    field_simp
    ring

theorem scale_pair_norms (hε : ε ≠ 0) (s t : F) {u v : V8 F} {ν : F} (hu : Q8 u = ν)
    (hv : Q8 v = ε * ν) (huv : B8 u v = 0) :
    Q8 (s • u + (-(t / ε)) • v) = (s ^ 2 + t ^ 2 / ε) * ν ∧
      Q8 (t • u + s • v) = ε * ((s ^ 2 + t ^ 2 / ε) * ν) ∧
      B8 (s • u + (-(t / ε)) • v) (t • u + s • v) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Q8_lin, hu, hv, huv]
    field_simp
    ring
  · rw [Q8_lin, hu, hv, huv]
    field_simp
    ring
  · simp only [B8_lin_left, B8_lin_right, B8_comm v u, B8_self, hu, hv, huv]
    field_simp
    ring

theorem scale_pair_inv (s t : F) (u v : V8 F) :
    (s ^ 2 + t ^ 2 / ε) • u = s • (s • u + (-(t / ε)) • v) + (t / ε) • (t • u + s • v) ∧
      (s ^ 2 + t ^ 2 / ε) • v = (-t) • (s • u + (-(t / ε)) • v) + s • (t • u + s • v) := by
  constructor
  · module
  · module

theorem exists_norm_eq [Finite F] (hodd : Odd (Nat.card F)) (hε : ε ≠ 0) (c : F) :
    ∃ s t : F, s ^ 2 + t ^ 2 / ε = c := by
  have := Fintype.ofFinite F
  have hodd' : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2) (g := Polynomial.C (1 / ε) * Polynomial.X ^ 2 +
      Polynomial.C 0 * Polynomial.X + Polynomial.C (-c))
    (by rw [Polynomial.degree_X_pow]; rfl)
    (by
      rw [Polynomial.degree_quadratic (one_div_ne_zero hε)]) hodd'
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

end CFSG.ClassicalInvolution.PhanQ
