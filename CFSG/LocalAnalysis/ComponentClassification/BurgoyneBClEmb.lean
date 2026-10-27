module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClBasic

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix
open scoped commutatorElement

theorem ring_expand_conj {A : Type*} [Ring A] (X Y Q : A) :
    (1 + Y) * Q * (1 + X) = Q + Q * X + Y * Q + Y * Q * X := by
  noncomm_ring

theorem ring_expand_mul {A : Type*} [Ring A] (X Y : A) :
    (1 + X) * (1 + Y) = 1 + (X + Y + X * Y) := by
  noncomm_ring

theorem ring_expand_isometry {A : Type*} [Ring A] (G M M' : A) :
    G * (M - 1) + (M' - 1) * G + (M' - 1) * G * (M - 1) = M' * G * M - G := by
  noncomm_ring

section Emb

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

@[expose] def embT (E : Matrix n m R) (F : Matrix m n R) (M : Matrix m m R) : Matrix n n R :=
  1 + E * (M - 1) * F

variable {E : Matrix n m R} {F : Matrix m n R}

omit [Fintype n] in
theorem embT_one : embT E F 1 = 1 := by
  rw [embT, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem embT_mul (hFE : F * E = 1) (M N : Matrix m m R) :
    embT E F (M * N) = embT E F M * embT E F N := by
  have key : E * (M - 1) * F * (E * (N - 1) * F) = E * ((M - 1) * (N - 1)) * F := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F E, hFE, Matrix.one_mul]
  have hMN : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  have e : E * (M * N - 1) * F = E * (M - 1) * F + E * (N - 1) * F +
      E * (M - 1) * F * (E * (N - 1) * F) := by
    rw [key, hMN, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  rw [embT, embT, embT, e, ring_expand_mul]

@[expose] def embHom (hFE : F * E = 1) : Matrix m m R →* Matrix n n R where
  toFun := embT E F
  map_one' := embT_one
  map_mul' := embT_mul hFE

theorem det_embT (hFE : F * E = 1) (M : Matrix m m R) : (embT E F M).det = M.det := by
  rw [embT, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hFE, Matrix.one_mul,
    show (1 : Matrix m m R) + (M - 1) = M by abel]

@[expose] def embSL (hFE : F * E = 1) : SpecialLinearGroup m R →* SpecialLinearGroup n R where
  toFun g := ⟨embT E F g, by rw [det_embT hFE, g.2]⟩
  map_one' := Subtype.ext embT_one
  map_mul' g h := Subtype.ext (embT_mul hFE (g : Matrix m m R) h)

theorem coe_embSL (hFE : F * E = 1) (g : SpecialLinearGroup m R) :
    ((embSL hFE g : SpecialLinearGroup n R) : Matrix n n R) = embT E F g := rfl

theorem embT_isometry (hFE : F * E = 1) {Q : Matrix n n R} {G : Matrix m m R}
    (h1 : Eᵀ * Q = G * F) (h2 : Q * E = Fᵀ * G) {M : Matrix m m R} (hM : Mᵀ * G * M = G) :
    (embT E F M)ᵀ * Q * embT E F M = Q := by
  have hT : (embT E F M)ᵀ = 1 + Fᵀ * (Mᵀ - 1) * Eᵀ := by
    simp only [embT, transpose_add, transpose_one, transpose_mul, transpose_sub,
      Matrix.mul_assoc]
  have e1 : Q * (E * (M - 1) * F) = Fᵀ * (G * (M - 1)) * F := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
    simp only [Matrix.mul_assoc]
  have e2 : Fᵀ * (Mᵀ - 1) * Eᵀ * Q = Fᵀ * ((Mᵀ - 1) * G) * F := by
    rw [Matrix.mul_assoc, h1]
    simp only [Matrix.mul_assoc]
  have e3 : Fᵀ * (Mᵀ - 1) * Eᵀ * Q * (E * (M - 1) * F) =
      Fᵀ * ((Mᵀ - 1) * G * (M - 1)) * F := by
    rw [e2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F E, hFE, Matrix.one_mul]
  have e4 : G * (M - 1) + (Mᵀ - 1) * G + (Mᵀ - 1) * G * (M - 1) = 0 := by
    rw [ring_expand_isometry, hM, sub_self]
  have e5 : Fᵀ * (G * (M - 1)) * F + Fᵀ * ((Mᵀ - 1) * G) * F +
      Fᵀ * ((Mᵀ - 1) * G * (M - 1)) * F = 0 := by
    rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, e4,
      Matrix.mul_zero, Matrix.zero_mul]
  rw [hT, embT, ring_expand_conj, e3, e2, e1, add_assoc Q, add_assoc Q, e5, add_zero]

theorem embT_commute {A : Matrix n n R} {A₄ : Matrix m m R} (hAE : A * E = E * A₄)
    (hFA : F * A = A₄ * F) {M : Matrix m m R} (hM : A₄ * M = M * A₄) :
    A * embT E F M = embT E F M * A := by
  have hM1 : A₄ * (M - 1) = (M - 1) * A₄ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hM, Matrix.mul_one, Matrix.one_mul]
  rw [embT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  calc A * (E * (M - 1) * F) = (A * E) * (M - 1) * F := by simp only [Matrix.mul_assoc]
    _ = E * (A₄ * (M - 1)) * F := by rw [hAE]; simp only [Matrix.mul_assoc]
    _ = E * (M - 1) * (A₄ * F) := by rw [hM1]; simp only [Matrix.mul_assoc]
    _ = E * (M - 1) * F * A := by rw [← hFA]; simp only [Matrix.mul_assoc]

end Emb

section Field

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n] {E : Matrix n m K} {F : Matrix m n K}

theorem embT_neg_one_ne_smul (h2 : (2 : K) ≠ 0) [Nonempty m] (hFE : F * E = 1)
    (hmn : Fintype.card m < Fintype.card n) (c : K) : embT E F (-1) ≠ c • 1 := by
  intro h
  have e1 : embT E F (-1) = 1 - (2 : K) • (E * F) := by
    rw [embT, show (-1 : Matrix m m K) - 1 = -((2 : K) • 1) by rw [two_smul]; abel,
      Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one, Matrix.neg_mul, Matrix.smul_mul,
      sub_eq_add_neg]
  have hE : (c + 1) • E = 0 := by
    have h' : embT E F (-1) * E = (c • (1 : Matrix n n K)) * E := by rw [h]
    rw [e1, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, hFE,
      Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at h'
    rw [add_smul, one_smul, ← h', two_smul]
    abel
  have hE0 : E ≠ 0 := by
    intro h0
    rw [h0, Matrix.mul_zero] at hFE
    obtain ⟨i⟩ := ‹Nonempty m›
    have := congrFun (congrFun hFE i) i
    simp at this
  have hc : c = -1 := by
    by_contra hc
    have hc1 : c + 1 ≠ 0 := fun h' => hc (eq_neg_of_add_eq_zero_left h')
    exact hE0 ((smul_eq_zero.1 hE).resolve_left hc1)
  subst hc
  have hEF : E * F = 1 := by
    rw [e1, neg_one_smul] at h
    have h3 : (2 : K) • (E * F) = (2 : K) • 1 := by
      calc (2 : K) • (E * F) = 1 - (1 - (2 : K) • (E * F)) := by abel
        _ = (2 : K) • 1 := by rw [h, two_smul]; abel
    exact smul_right_injective _ h2 h3
  have h4 := Matrix.rank_mul_le_left E F
  have h5 := Matrix.rank_le_card_width E
  rw [hEF, Matrix.rank_one] at h4
  omega

end Field

section Quat

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : Matrix ι ι K}

@[expose] def quatW (x y : Matrix ι ι K) : Matrix ι ι K := (2 : K)⁻¹ • (1 + x + y + x * y)

@[expose] def quatW' (x y : Matrix ι ι K) : Matrix ι ι K := (2 : K)⁻¹ • (1 - x - y - x * y)

section Rel

variable (hx : x * x = -1) (hy : y * y = -1) (hyx : y * x = -(x * y))

include hx in
theorem quat_x_x (t : Matrix ι ι K) : x * (x * t) = -t := by
  rw [← Matrix.mul_assoc, hx, Matrix.neg_mul, Matrix.one_mul]

omit [DecidableEq ι] in
include hyx in
theorem quat_y_x (t : Matrix ι ι K) : y * (x * t) = -(x * (y * t)) := by
  rw [← Matrix.mul_assoc, hyx, Matrix.neg_mul, Matrix.mul_assoc]

include hx hy hyx in
theorem quat_mul_conj :
    (1 + x + y + x * y) * (1 - x - y - x * y) = (4 : K) • (1 : Matrix ι ι K) := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    hx, hy, hyx, quat_x_x hx, quat_y_x hyx, Matrix.mul_neg, neg_neg]
  rw [show (4 : K) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul]
  abel

include hx hy hyx in
theorem quat_conj_mul :
    (1 - x - y - x * y) * (1 + x + y + x * y) = (4 : K) • (1 : Matrix ι ι K) := by
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    hx, hy, hyx, quat_x_x hx, quat_y_x hyx, Matrix.mul_neg, neg_neg]
  rw [show (4 : K) = 1 + 1 + 1 + 1 by norm_num, add_smul, add_smul, add_smul, one_smul]
  abel

omit [Fintype ι] [DecidableEq ι] in
theorem half_smul_half (h2 : (2 : K) ≠ 0) (M : Matrix ι ι K) :
    (2 : K)⁻¹ • ((2 : K)⁻¹ • ((4 : K) • M)) = M := by
  rw [smul_smul, smul_smul, show (2 : K)⁻¹ * (2 : K)⁻¹ * 4 = 1 by field_simp; norm_num,
    one_smul]

include hx hy hyx in
theorem quatW_mul_quatW' (h2 : (2 : K) ≠ 0) : quatW x y * quatW' x y = 1 := by
  rw [quatW, quatW', Matrix.smul_mul, Matrix.mul_smul, quat_mul_conj hx hy hyx,
    half_smul_half h2]

include hx hy hyx in
theorem quatW'_mul_quatW (h2 : (2 : K) ≠ 0) : quatW' x y * quatW x y = 1 := by
  rw [quatW, quatW', Matrix.smul_mul, Matrix.mul_smul, quat_conj_mul hx hy hyx,
    half_smul_half h2]

include hx hy hyx in
theorem quatW_mul_y : quatW x y * y = (x * y) * quatW x y := by
  rw [quatW, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    hx, hy, hyx, quat_x_x hx, quat_y_x hyx, Matrix.mul_neg, neg_neg]
  abel

include hx hy hyx in
theorem quatW_mul_xy : quatW x y * (x * y) = x * quatW x y := by
  rw [quatW, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc,
    hx, hy, quat_x_x hx, quat_y_x hyx, Matrix.mul_neg, neg_neg]
  abel

include hx hy hyx in
theorem quatW_isometry (h2 : (2 : K) ≠ 0) {Q : Matrix ι ι K} (hxQ : xᵀ * Q * x = Q)
    (hyQ : yᵀ * Q * y = Q) : (quatW x y)ᵀ * Q * quatW x y = Q := by
  have hinv : ∀ {u : Matrix ι ι K}, u * u = -1 → uᵀ * Q * u = Q → uᵀ * Q = -(Q * u) := by
    intro u hu huQ
    calc uᵀ * Q = uᵀ * Q * (u * -u) := by rw [Matrix.mul_neg, hu, neg_neg, Matrix.mul_one]
      _ = -(Q * u) := by rw [← Matrix.mul_assoc, huQ, Matrix.mul_neg]
  have hxT := hinv hx hxQ
  have hyT := hinv hy hyQ
  have hT : (quatW x y)ᵀ * Q = Q * quatW' x y := by
    rw [quatW, quatW', transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    rw [transpose_add, transpose_add, transpose_add, transpose_one, transpose_mul,
      Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, hxT, hyT,
      Matrix.mul_assoc, hxT, Matrix.mul_neg, ← Matrix.mul_assoc, hyT, Matrix.neg_mul,
      neg_neg, Matrix.mul_assoc, hyx, Matrix.mul_neg]
    simp only [Matrix.mul_sub, Matrix.mul_one]
    abel
  rw [hT, Matrix.mul_assoc, quatW'_mul_quatW hx hy hyx h2, Matrix.mul_one]

end Rel

theorem quatW_commute {A : Matrix ι ι K} (hxA : A * x = x * A) (hyA : A * y = y * A) :
    A * quatW x y = quatW x y * A := by
  rw [quatW, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hxA, hyA, ← Matrix.mul_assoc, hxA, Matrix.mul_assoc, hyA, Matrix.mul_assoc]

end Quat

theorem commutatorElement_quat {G : Type*} [Group G] {x y z w : G} (hz2 : z ^ 2 = 1)
    (hxz : x ^ 2 = z) (hyz : y ^ 2 = z) (hxy : x * y = z * (y * x))
    (hw1 : w * y * w⁻¹ = x * y) (hw2 : w * (x * y) * w⁻¹ = x) :
    ⁅w, y⁆ = x ∧ ⁅w, x * y⁆ = y := by
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def, hw1, mul_inv_cancel_right]
  · rw [commutatorElement_def, hw2, mul_inv_eq_iff_eq_mul]
    have hzz : z * z = 1 := by rw [← pow_two, hz2]
    have hzx : z * x = x * z := by rw [← hxz, pow_two, mul_assoc]
    have hyy : y * y = z := by rw [← pow_two, hyz]
    have hyx : y * x = z * (x * y) := by
      rw [hxy, ← mul_assoc, hzz, one_mul]
    have e : y * (x * y) = x := by
      calc y * (x * y) = (y * x) * y := (mul_assoc _ _ _).symm
        _ = z * (x * y) * y := by rw [hyx]
        _ = z * x * (y * y) := by simp only [mul_assoc]
        _ = z * x * z := by rw [hyy]
        _ = x * (z * z) := by rw [hzx, mul_assoc]
        _ = x := by rw [hzz, mul_one]
    exact e.symm

end CFSG.ComponentClassification.Burgoyne.Cl
