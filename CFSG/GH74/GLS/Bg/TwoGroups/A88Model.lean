module

public import CFSG.GH74.GLS.Bg.TwoGroups.A44Data

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace A44

open Multiplicative

structure M8 where
  a : ZMod 8
  b : ZMod 8
  c : ZMod 8
  d : ZMod 8

instance : DecidableEq M8 := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b ∧ x.c = y.c ∧ x.d = y.d) (by
    cases x; cases y; simp)

instance : Fintype M8 :=
  Fintype.ofEquiv (ZMod 8 × ZMod 8 × ZMod 8 × ZMod 8)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
      invFun := fun x => (x.a, x.b, x.c, x.d)
      left_inv := fun t => rfl
      right_inv := fun x => by cases x; rfl }

namespace M8

@[expose] def mul (x y : M8) : M8 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

@[expose] def one : M8 := ⟨1, 0, 0, 1⟩

@[expose] def det (x : M8) : ZMod 8 := x.a * x.d - x.b * x.c

@[expose] def IsInv (x : M8) : Prop := x.det.val % 2 = 1

instance (x : M8) : Decidable x.IsInv := by unfold IsInv; infer_instance

@[expose] def act (x : M8) (v : ZMod 8 × ZMod 8) : ZMod 8 × ZMod 8 :=
  (x.a * v.1 + x.b * v.2, x.c * v.1 + x.d * v.2)

@[expose] def red (x : M8) : M4 :=
  ⟨ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) x.a, ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) x.b,
    ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) x.c,
    ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) x.d⟩

theorem act_mul (x y : M8) (v : ZMod 8 × ZMod 8) : (mul x y).act v = x.act (y.act v) := by
  simp only [act, mul]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem act_one (v : ZMod 8 × ZMod 8) : one.act v = v := by
  simp [act, one]

theorem ext_act {x y : M8} (h1 : x.act (1, 0) = y.act (1, 0)) (h2 : x.act (0, 1) = y.act (0, 1)) :
    x = y := by
  cases x; cases y
  simp [act] at h1 h2
  simp [h1.1, h1.2, h2.1, h2.2]

theorem red_mul (x y : M8) : red (mul x y) = M4.mul (red x) (red y) := by
  simp only [red, mul, M4.mul, map_add, map_mul]

theorem red_one : red one = M4.one := by
  simp [red, one, M4.one]

theorem det_red (x : M8) : (red x).det = ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) x.det := by
  simp only [red, M4.det, M8.det, map_sub, map_mul]

theorem cast_odd : ∀ d : ZMod 8, d.val % 2 = 1 →
    ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) d = 1 ∨
      ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) d = 3 := by decide +kernel

theorem isInv_red (x : M8) (hx : x.IsInv) : (red x).IsInv := by
  unfold M4.IsInv
  rw [det_red]
  exact cast_odd _ hx

end M8

@[expose] def toM8 (φ : MulAut Z8Z8) : M8 :=
  ⟨(toAdd (φ (ofAdd (1, 0)))).1, (toAdd (φ (ofAdd (0, 1)))).1,
   (toAdd (φ (ofAdd (1, 0)))).2, (toAdd (φ (ofAdd (0, 1)))).2⟩

theorem ofAdd_eq_prod8 (v : ZMod 8 × ZMod 8) :
    (ofAdd v : Z8Z8) = (ofAdd (1, 0) : Z8Z8) ^ v.1.val * (ofAdd (0, 1) : Z8Z8) ^ v.2.val := by
  rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp

theorem toAdd_phi8 (φ : MulAut Z8Z8) (v : ZMod 8 × ZMod 8) :
    toAdd (φ (ofAdd v)) = (toM8 φ).act v := by
  rw [ofAdd_eq_prod8, map_mul, map_pow, map_pow, toAdd_mul, toAdd_pow, toAdd_pow]
  simp only [toM8, M8.act]
  refine Prod.ext ?_ ?_ <;>
    simp [nsmul_eq_mul, mul_comm]

theorem ofAdd_toAdd_phi8 (φ : MulAut Z8Z8) (v : ZMod 8 × ZMod 8) :
    φ (ofAdd v) = ofAdd ((toM8 φ).act v) := by
  rw [← toAdd_phi8, ofAdd_toAdd]

theorem toM8_isInv (φ : MulAut Z8Z8) : (toM8 φ).IsInv := by
  by_contra hne
  have key : ∀ a b c d : ZMod 8, ¬ (M8.mk a b c d).IsInv →
      ∃ v : ZMod 8 × ZMod 8, v ≠ 0 ∧ (M8.mk a b c d).act v = 0 := by
    decide +kernel
  obtain ⟨v, hv0, hv⟩ := key (toM8 φ).a (toM8 φ).b (toM8 φ).c (toM8 φ).d hne
  apply hv0
  have h1 : φ (ofAdd v) = φ (ofAdd 0) := by
    rw [ofAdd_toAdd_phi8, hv]; simp
  have h2 := φ.injective h1
  exact ofAdd.injective h2

theorem toAdd_phi_mul8 (φ ψ : MulAut Z8Z8) (v : ZMod 8 × ZMod 8) :
    toAdd ((φ * ψ) (ofAdd v)) = (M8.mul (toM8 φ) (toM8 ψ)).act v := by
  rw [MulAut.mul_apply, ofAdd_toAdd_phi8, ofAdd_toAdd_phi8, toAdd_ofAdd, M8.act_mul]

theorem toM8_mul (φ ψ : MulAut Z8Z8) : toM8 (φ * ψ) = M8.mul (toM8 φ) (toM8 ψ) := by
  apply M8.ext_act
  · rw [← toAdd_phi8, toAdd_phi_mul8]
  · rw [← toAdd_phi8, toAdd_phi_mul8]

theorem toM8_one : toM8 (1 : MulAut Z8Z8) = M8.one := by
  apply M8.ext_act
  · rw [← toAdd_phi8, M8.act_one]; rfl
  · rw [← toAdd_phi8, M8.act_one]; rfl

@[expose] noncomputable def rho8 : MulAut Z8Z8 →* G96 where
  toFun φ := G96.mk (M8.red (toM8 φ)) (M8.isInv_red _ (toM8_isInv φ))
  map_one' := Subtype.ext (show M8.red (toM8 (1 : MulAut Z8Z8)) = M4.one by
    rw [toM8_one, M8.red_one])
  map_mul' φ ψ := Subtype.ext (show M8.red (toM8 (φ * ψ)) =
      M4.mul (M8.red (toM8 φ)) (M8.red (toM8 ψ)) by
    rw [toM8_mul, M8.red_mul])

theorem lem22_check : ∀ a b c d : ZMod 8, (M8.mk a b c d).IsInv →
    M8.mul (M8.mk a b c d) (M8.mk a b c d) = M8.one → M8.red (M8.mk a b c d) ∈ V4list →
    M8.red (M8.mk a b c d) = M4.one := by decide +kernel

theorem K0_sq_V : ∀ x ∈ K0list, M4.mul x x = M4.one → x ∈ V4list := by decide +kernel

end A44

end CFSG.GH74.GLS.Bg.TwoGroups
