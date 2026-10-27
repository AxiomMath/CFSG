module

public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin

abbrev V8 (F : Type) : Type := Fin 4 ⊕ Fin 4 → F

variable {F : Type} [Field F]

noncomputable abbrev Q8 (x : V8 F) : F := quadPlus 4 F x

noncomputable abbrev B8 (x y : V8 F) : F := polar (quadPlus 4 F) x y

section Form

theorem B8_comm (x y : V8 F) : B8 x y = B8 y x := polar_comm _ _ _

theorem B8_self (x : V8 F) : B8 x x = 2 * Q8 x := by
  rw [B8, polar_self, nsmul_eq_mul]
  norm_num

theorem B8_lin_left (a b : F) (x y z : V8 F) :
    B8 (a • x + b • y) z = a * B8 x z + b * B8 y z := by
  rw [B8, polar_add_left, polar_smul_left, polar_smul_left]
  simp only [smul_eq_mul]

theorem B8_lin_right (a b : F) (x y z : V8 F) :
    B8 z (a • x + b • y) = a * B8 z x + b * B8 z y := by
  rw [B8_comm, B8_lin_left, B8_comm x, B8_comm y]

theorem Q8_lin (a b : F) (x y : V8 F) :
    Q8 (a • x + b • y) = a ^ 2 * Q8 x + b ^ 2 * Q8 y + a * b * B8 x y := by
  rw [Q8, QuadraticMap.map_add (quadPlus 4 F), QuadraticMap.map_smul, QuadraticMap.map_smul,
    polar_smul_left, polar_smul_right]
  simp only [smul_eq_mul, B8]
  ring

end Form

section Pair

@[ext] structure NPair (ε : F) where
  x : V8 F
  y : V8 F
  hx : Q8 x = 1
  hy : Q8 y = ε
  hxy : B8 x y = 0

variable {ε : F}

@[expose] def NPair.rot (hε : ε ≠ 0) (s t : F) (h : s ^ 2 + t ^ 2 / ε = 1) (z : NPair ε) :
    NPair ε where
  x := s • z.x + (-(t / ε)) • z.y
  y := t • z.x + s • z.y
  hx := by
    have h' := h
    field_simp at h'
    rw [Q8_lin, z.hx, z.hy, z.hxy]
    field_simp
    linear_combination h'
  hy := by
    have h' := h
    field_simp at h'
    rw [Q8_lin, z.hx, z.hy, z.hxy]
    linear_combination h'
  hxy := by
    rw [B8_lin_left, B8_lin_right, B8_lin_right, B8_self, B8_self, z.hx, z.hy, z.hxy,
      B8_comm z.y z.x, z.hxy]
    field_simp
    ring

theorem NPair.rot_x (hε : ε ≠ 0) (s t : F) (h : s ^ 2 + t ^ 2 / ε = 1) (z : NPair ε) :
    (z.rot hε s t h).x = s • z.x + (-(t / ε)) • z.y := rfl

theorem NPair.rot_y (hε : ε ≠ 0) (s t : F) (h : s ^ 2 + t ^ 2 / ε = 1) (z : NPair ε) :
    (z.rot hε s t h).y = t • z.x + s • z.y := rfl

theorem NPair.rot_rot_neg (hε : ε ≠ 0) (s t : F) (h : s ^ 2 + t ^ 2 / ε = 1)
    (h' : s ^ 2 + (-t) ^ 2 / ε = 1) (z : NPair ε) :
    (z.rot hε s t h).rot hε s (-t) h' = z := by
  have e1 : s * s + -(-t / ε) * t = (1 : F) := by
    have h'' := h
    field_simp at h'' ⊢
    linear_combination h''
  have e2 : -t * (-(t / ε)) + s * s = (1 : F) := by
    have h'' := h
    field_simp at h'' ⊢
    linear_combination h''
  ext1
  · show s • (s • z.x + (-(t / ε)) • z.y) + (-(-t / ε)) • (t • z.x + s • z.y) = z.x
    calc _ = (s * s + -(-t / ε) * t) • z.x + (s * (-(t / ε)) + -(-t / ε) * s) • z.y := by module
      _ = z.x := by
        have e0 : s * (-(t / ε)) + -(-t / ε) * s = (0 : F) := by ring
        rw [e1, e0]
        simp
  · show (-t) • (s • z.x + (-(t / ε)) • z.y) + s • (t • z.x + s • z.y) = z.y
    calc _ = (-t * s + s * t) • z.x + (-t * (-(t / ε)) + s * s) • z.y := by module
      _ = z.y := by
        have e0 : -t * s + s * t = (0 : F) := by ring
        rw [e2, e0]
        simp

end Pair

section Col

variable {ε : F}

@[expose] def ColP (ε : F) (z w : NPair ε) : Prop :=
  B8 z.y w.y = ε * B8 z.x w.x ∧ B8 z.x w.y + B8 z.y w.x = 0 ∧
    B8 z.x w.x ^ 2 + B8 z.y w.x ^ 2 / ε ≠ 4

theorem ColP.symm {z w : NPair ε} (h : ColP ε z w) : ColP ε w z := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [B8_comm w.y z.y, B8_comm w.x z.x, h1]
  · rw [B8_comm w.x z.y, B8_comm w.y z.x, ← h2]
    ring
  · rw [B8_comm w.x z.x, B8_comm w.y z.x]
    have : B8 z.x w.y = -B8 z.y w.x := by linear_combination h2
    rw [this] at *
    intro h4
    apply h3
    rw [← h4]
    ring

theorem colP_rot_right_of (hε : ε ≠ 0) (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1) {z w : NPair ε}
    (h : ColP ε z w) : ColP ε z (w.rot hε s t hst) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hr : B8 z.x w.y = -B8 z.y w.x := by linear_combination h2
  have e : ε * (-(t / ε)) = -t := by field_simp
  have e'' : t / ε * ε = t := by field_simp
  have c1 : B8 z.y (w.rot hε s t hst).y = ε * B8 z.x (w.rot hε s t hst).x := by
    simp only [NPair.rot_x, NPair.rot_y, B8_lin_right]
    linear_combination s * h1 + t * h2 - (B8 z.x w.y) * e
  have c2 : B8 z.x (w.rot hε s t hst).y + B8 z.y (w.rot hε s t hst).x = 0 := by
    simp only [NPair.rot_x, NPair.rot_y, B8_lin_right]
    linear_combination s * h2 - (t / ε) * h1 - (B8 z.x w.x) * e''
  refine ⟨c1, c2, ?_⟩
  simp only [NPair.rot_x, B8_lin_right]
  intro h4
  apply h3
  have e : (s * B8 z.x w.x + -(t / ε) * B8 z.x w.y) ^ 2 +
      (s * B8 z.y w.x + -(t / ε) * B8 z.y w.y) ^ 2 / ε =
      (B8 z.x w.x ^ 2 + B8 z.y w.x ^ 2 / ε) * (s ^ 2 + t ^ 2 / ε) := by
    rw [h1, hr]
    field_simp
    ring
  rw [e, hst, mul_one] at h4
  exact h4

theorem colP_rot_right (hε : ε ≠ 0) (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1) {z w : NPair ε} :
    ColP ε z (w.rot hε s t hst) ↔ ColP ε z w := by
  refine ⟨fun h => ?_, colP_rot_right_of hε s t hst⟩
  have hst' : s ^ 2 + (-t) ^ 2 / ε = 1 := by rw [neg_sq]; exact hst
  have := colP_rot_right_of hε s (-t) hst' h
  rwa [NPair.rot_rot_neg hε s t hst hst'] at this

theorem colP_rot_left (hε : ε ≠ 0) (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1) {z w : NPair ε} :
    ColP ε (z.rot hε s t hst) w ↔ ColP ε z w :=
  ⟨fun h => ((colP_rot_right hε s t hst).1 h.symm).symm, fun h =>
    (colP_rot_right_of hε s t hst h.symm).symm⟩

end Col

end CFSG.ClassicalInvolution.PhanQ
