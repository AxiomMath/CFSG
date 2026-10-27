module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLinX

public section

namespace CFSG.OddStandard.SmallF3.FritzII.FzL59BLin

variable {G : Type} [Group G]

structure LinData (ε : Bool) (fn : N →* G) (y u : G) : Prop where
  y_sq : y * y = 1
  u_sq : u * u = 1
  hy : ∀ n, y * fn n = fn (xiN n) * y
  hu : ∀ n, u * fn n = fn (psiN ε n) * u
  hyu : y * u = fn (cN ε) * (u * y)
  zeta : fn zetaN = 1

@[expose] def yp (y : G) (e : Bool) : G := if e then y else 1

@[expose] def up (u : G) (f : Bool) : G := if f then u else 1

@[expose] def phi (fn : N →* G) (y u : G) (x : X) : G := fn x.1 * yp y x.2.1 * up u x.2.2

variable {ε : Bool} {fn : N →* G} {y u : G}

theorem LinData.up_fn (D : LinData ε fn y u) (f : Bool) (n : N) :
    up u f * fn n = fn (twF ε f n) * up u f := by
  cases f
  · simp [up, twF]
  · simpa [up, twF] using D.hu n

theorem LinData.yp_fn (D : LinData ε fn y u) (e : Bool) (n : N) :
    yp y e * fn n = fn (twE e n) * yp y e := by
  cases e
  · simp [yp, twE]
  · simpa [yp, twE] using D.hy n

theorem LinData.up_yp (D : LinData ε fn y u) (f e : Bool) :
    up u f * yp y e = fn (if f && e then (cN ε)⁻¹ else 1) * (yp y e * up u f) := by
  cases f <;> cases e
  · simp [up, yp]
  · simp [up, yp]
  · simp [up, yp]
  · have h := D.hyu
    have h2 : u * y = (fn (cN ε))⁻¹ * (y * u) := by
      rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
    simpa [up, yp, map_inv] using h2

theorem LinData.yp_yp (D : LinData ε fn y u) (e e' : Bool) :
    yp y e * yp y e' = yp y (e ^^ e') := by
  cases e <;> cases e' <;> simp [yp, D.y_sq]

theorem LinData.up_up (D : LinData ε fn y u) (f f' : Bool) :
    up u f * up u f' = up u (f ^^ f') := by
  cases f <;> cases f' <;> simp [up, D.u_sq]

theorem twE_one (e : Bool) : twE e (1 : N) = 1 := by
  cases e <;> simp [twE]

theorem phi_star_aux {A B C E E' F F' FB M c EE FF : G}
    (h1 : F * M = FB * F) (h2 : E * FB = B * E) (h3 : F * E' = c * (E' * F))
    (h4 : E * c = C * E) (h5 : E * E' = EE) (h6 : F * F' = FF) :
    A * B * C * EE * FF = A * E * F * (M * E' * F') := by
  subst h5 h6
  calc A * B * C * (E * E') * (F * F')
      = A * (B * ((C * E) * ((E' * F) * F'))) := by simp only [mul_assoc]
    _ = A * (B * ((E * c) * ((E' * F) * F'))) := by rw [h4]
    _ = A * ((B * E) * ((c * (E' * F)) * F')) := by simp only [mul_assoc]
    _ = A * ((E * FB) * ((F * E') * F')) := by rw [h2, h3]
    _ = A * (E * ((FB * F) * (E' * F'))) := by simp only [mul_assoc]
    _ = A * (E * ((F * M) * (E' * F'))) := by rw [h1]
    _ = A * E * F * (M * E' * F') := by simp only [mul_assoc]

theorem LinData.phi_star (D : LinData ε fn y u) (x z : X) :
    phi fn y u (star ε x z) = phi fn y u x * phi fn y u z := by
  obtain ⟨n, e, f⟩ := x
  obtain ⟨m, e', f'⟩ := z
  have hC : (if f && e' then twE e (cN ε)⁻¹ else 1) = twE e (if f && e' then (cN ε)⁻¹ else 1) := by
    split_ifs
    · rfl
    · exact (twE_one e).symm
  show fn (n * twE e (twF ε f m) * (if f && e' then twE e (cN ε)⁻¹ else 1)) *
      yp y (e ^^ e') * up u (f ^^ f') = fn n * yp y e * up u f * (fn m * yp y e' * up u f')
  rw [hC, map_mul, map_mul]
  exact phi_star_aux (D.up_fn f m) (D.yp_fn e (twF ε f m)) (D.up_yp f e')
    (D.yp_fn e (if f && e' then (cN ε)⁻¹ else 1)) (D.yp_yp e e') (D.up_up f f')

theorem LinData.phi_ktr (D : LinData ε fn y u) (x : X) : phi fn y u (ktr x) = phi fn y u x := by
  obtain ⟨n, e, f⟩ := x
  show fn (n * zetaN) * yp y e * up u f = fn n * yp y e * up u f
  rw [map_mul, D.zeta, mul_one]

theorem phi_one (fn : N →* G) (y u : G) : phi fn y u oneX = 1 := by
  simp [phi, oneX, yp, up]

end CFSG.OddStandard.SmallF3.FritzII.FzL59BLin
