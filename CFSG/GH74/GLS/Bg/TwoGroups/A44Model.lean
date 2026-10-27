module

public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace A44

structure M4 where
  a : ZMod 4
  b : ZMod 4
  c : ZMod 4
  d : ZMod 4

instance : DecidableEq M4 := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b ∧ x.c = y.c ∧ x.d = y.d) (by
    cases x; cases y; simp)

instance : Fintype M4 :=
  Fintype.ofEquiv (ZMod 4 × ZMod 4 × ZMod 4 × ZMod 4)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
      invFun := fun x => (x.a, x.b, x.c, x.d)
      left_inv := fun t => rfl
      right_inv := fun x => by cases x; rfl }

namespace M4

@[expose] def mul (x y : M4) : M4 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

@[expose] def one : M4 := ⟨1, 0, 0, 1⟩

@[expose] def det (x : M4) : ZMod 4 := x.a * x.d - x.b * x.c

@[expose] def IsInv (x : M4) : Prop := x.det = 1 ∨ x.det = 3

instance (x : M4) : Decidable x.IsInv := by unfold IsInv; infer_instance

@[expose] def act (x : M4) (v : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 :=
  (x.a * v.1 + x.b * v.2, x.c * v.1 + x.d * v.2)

@[expose] def inv (x : M4) : M4 :=
  ⟨x.det * x.d, -(x.det * x.b), -(x.det * x.c), x.det * x.a⟩

theorem mul_assoc (x y z : M4) : mul (mul x y) z = mul x (mul y z) := by
  cases x; cases y; cases z
  simp only [mul, M4.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem one_mul (x : M4) : mul one x = x := by
  cases x; simp [mul, one]

theorem mul_one (x : M4) : mul x one = x := by
  cases x; simp [mul, one]

theorem mul_inv : ∀ x : M4, x.IsInv → mul x x.inv = one := by decide +kernel

theorem inv_mul : ∀ x : M4, x.IsInv → mul x.inv x = one := by decide +kernel

theorem isInv_inv : ∀ x : M4, x.IsInv → x.inv.IsInv := by decide +kernel

theorem isInv_mul : ∀ x y : M4, x.IsInv → y.IsInv → (mul x y).IsInv := by decide +kernel

theorem isInv_one : one.IsInv := by decide

theorem act_add (x : M4) (v w : ZMod 4 × ZMod 4) : x.act (v + w) = x.act v + x.act w := by
  simp only [act, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem act_mul (x y : M4) (v : ZMod 4 × ZMod 4) : (mul x y).act v = x.act (y.act v) := by
  simp only [act, mul]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

theorem act_one (v : ZMod 4 × ZMod 4) : one.act v = v := by
  simp [act, one]

theorem ext_act {x y : M4} (h1 : x.act (1, 0) = y.act (1, 0)) (h2 : x.act (0, 1) = y.act (0, 1)) :
    x = y := by
  cases x; cases y
  simp [act] at h1 h2
  simp [h1.1, h1.2, h2.1, h2.2]

end M4

@[expose] def G96 : Type := {x : M4 // x.IsInv}

instance : DecidableEq G96 := inferInstanceAs (DecidableEq {x : M4 // x.IsInv})
instance : Fintype G96 := inferInstanceAs (Fintype {x : M4 // x.IsInv})

instance : Group G96 where
  mul x y := ⟨M4.mul x.1 y.1, M4.isInv_mul _ _ x.2 y.2⟩
  one := ⟨M4.one, M4.isInv_one⟩
  inv x := ⟨x.1.inv, M4.isInv_inv _ x.2⟩
  mul_assoc x y z := Subtype.ext (M4.mul_assoc _ _ _)
  one_mul x := Subtype.ext (M4.one_mul _)
  mul_one x := Subtype.ext (M4.mul_one _)
  inv_mul_cancel x := Subtype.ext (M4.inv_mul _ x.2)

@[expose] def G96.mk (x : M4) (h : x.IsInv) : G96 := ⟨x, h⟩

@[simp] theorem G96.val_mk (x : M4) (h : x.IsInv) : (G96.mk x h).1 = x := rfl

@[simp] theorem G96.val_mul (x y : G96) : (x * y).1 = M4.mul x.1 y.1 := rfl
@[simp] theorem G96.val_one : (1 : G96).1 = M4.one := rfl
@[simp] theorem G96.val_inv (x : G96) : (x⁻¹).1 = x.1.inv := rfl

@[expose] def G96.act (x : G96) (v : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 := x.1.act v

@[expose] def toM4 (φ : MulAut Z4Z4) : M4 :=
  ⟨(Multiplicative.toAdd (φ (Multiplicative.ofAdd (1, 0)))).1,
   (Multiplicative.toAdd (φ (Multiplicative.ofAdd (0, 1)))).1,
   (Multiplicative.toAdd (φ (Multiplicative.ofAdd (1, 0)))).2,
   (Multiplicative.toAdd (φ (Multiplicative.ofAdd (0, 1)))).2⟩

theorem ofAdd_eq_prod (v : ZMod 4 × ZMod 4) :
    (Multiplicative.ofAdd v : Z4Z4) =
      (Multiplicative.ofAdd (1, 0) : Z4Z4) ^ v.1.val * (Multiplicative.ofAdd (0, 1) : Z4Z4) ^ v.2.val := by
  rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
  congr 1
  refine Prod.ext ?_ ?_ <;> simp

theorem toAdd_phi (φ : MulAut Z4Z4) (v : ZMod 4 × ZMod 4) :
    Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) = (toM4 φ).act v := by
  rw [ofAdd_eq_prod, map_mul, map_pow, map_pow, toAdd_mul, toAdd_pow, toAdd_pow]
  simp only [toM4, M4.act]
  refine Prod.ext ?_ ?_ <;>
    simp [nsmul_eq_mul, mul_comm]

theorem ofAdd_toAdd_phi (φ : MulAut Z4Z4) (v : ZMod 4 × ZMod 4) :
    φ (Multiplicative.ofAdd v) = Multiplicative.ofAdd ((toM4 φ).act v) := by
  rw [← toAdd_phi, ofAdd_toAdd]

theorem toM4_isInv (φ : MulAut Z4Z4) : (toM4 φ).IsInv := by
  by_contra hne
  have key : ∀ x : M4, ¬ x.IsInv → ∃ v : ZMod 4 × ZMod 4, v ≠ 0 ∧ x.act v = 0 := by decide +kernel
  obtain ⟨v, hv0, hv⟩ := key _ hne
  apply hv0
  have h1 : φ (Multiplicative.ofAdd v) = φ (Multiplicative.ofAdd 0) := by
    rw [ofAdd_toAdd_phi, hv]; simp
  have h2 := φ.injective h1
  exact Multiplicative.ofAdd.injective h2

theorem toAdd_phi_mul (φ ψ : MulAut Z4Z4) (v : ZMod 4 × ZMod 4) :
    Multiplicative.toAdd ((φ * ψ) (Multiplicative.ofAdd v)) =
      (M4.mul (toM4 φ) (toM4 ψ)).act v := by
  rw [MulAut.mul_apply, ofAdd_toAdd_phi, ofAdd_toAdd_phi, toAdd_ofAdd, M4.act_mul]

theorem toM4_mul (φ ψ : MulAut Z4Z4) : toM4 (φ * ψ) = M4.mul (toM4 φ) (toM4 ψ) := by
  apply M4.ext_act
  · rw [← toAdd_phi, toAdd_phi_mul]
  · rw [← toAdd_phi, toAdd_phi_mul]

theorem toM4_one : toM4 (1 : MulAut Z4Z4) = M4.one := by
  apply M4.ext_act
  · rw [← toAdd_phi, M4.act_one]; rfl
  · rw [← toAdd_phi, M4.act_one]; rfl

@[expose] def autOf (x : G96) : MulAut Z4Z4 where
  toFun b := Multiplicative.ofAdd (x.1.act (Multiplicative.toAdd b))
  invFun b := Multiplicative.ofAdd (x.1.inv.act (Multiplicative.toAdd b))
  left_inv b := by
    simp only [toAdd_ofAdd, ← M4.act_mul, M4.inv_mul x.1 x.2, M4.act_one, ofAdd_toAdd]
  right_inv b := by
    simp only [toAdd_ofAdd, ← M4.act_mul, M4.mul_inv x.1 x.2, M4.act_one, ofAdd_toAdd]
  map_mul' a b := by
    simp only [toAdd_mul, M4.act_add, ofAdd_add]

theorem toM4_autOf (x : G96) : toM4 (autOf x) = x.1 := by
  apply M4.ext_act
  · rw [← toAdd_phi]; rfl
  · rw [← toAdd_phi]; rfl

@[expose] def phiHom : MulAut Z4Z4 →* G96 where
  toFun φ := ⟨toM4 φ, toM4_isInv φ⟩
  map_one' := Subtype.ext toM4_one
  map_mul' φ ψ := Subtype.ext (toM4_mul φ ψ)

theorem phiHom_bijective : Function.Bijective phiHom := by
  constructor
  · intro φ ψ h
    have h1 : toM4 φ = toM4 ψ := congrArg Subtype.val h
    apply MulEquiv.ext
    intro b
    have : ∀ v, φ (Multiplicative.ofAdd v) = ψ (Multiplicative.ofAdd v) := by
      intro v
      rw [ofAdd_toAdd_phi, ofAdd_toAdd_phi, h1]
    have := this (Multiplicative.toAdd b)
    simpa using this
  · intro x
    exact ⟨autOf x, Subtype.ext (toM4_autOf x)⟩

@[expose] noncomputable def phi : MulAut Z4Z4 ≃* G96 :=
  MulEquiv.ofBijective phiHom phiHom_bijective

theorem phi_val (φ : MulAut Z4Z4) : (phi φ).1 = toM4 φ := rfl

theorem toAdd_phi' (φ : MulAut Z4Z4) (b : Z4Z4) :
    Multiplicative.toAdd (φ b) = (phi φ).1.act (Multiplicative.toAdd b) := by
  have := toAdd_phi φ (Multiplicative.toAdd b)
  rw [ofAdd_toAdd] at this
  exact this

@[expose] noncomputable def phiB {B : Type} [Group B] (e : B ≃* Z4Z4) : MulAut B ≃* G96 :=
  (MulAut.congr e).trans phi

theorem toAdd_phiB {B : Type} [Group B] (e : B ≃* Z4Z4) (φ : MulAut B) (b : B) :
    Multiplicative.toAdd (e (φ b)) = (phiB e φ).1.act (Multiplicative.toAdd (e b)) := by
  have h : MulAut.congr e φ (e b) = e (φ b) := by
    simp [MulAut.congr_apply]
  rw [← h, toAdd_phi']
  rfl

end A44

end CFSG.GH74.GLS.Bg.TwoGroups
