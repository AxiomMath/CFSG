module

public import Mathlib

public section

namespace CFSG.Fischer

structure F4 where
  code : Fin 4
deriving DecidableEq, Fintype

namespace F4

@[expose] def add (x y : F4) : F4 := ⟨x.code ^^^ y.code⟩

@[expose] def mulCode (x y : Fin 4) : Fin 4 :=
  let a0 := x.val % 2
  let a1 := x.val / 2
  let b0 := y.val % 2
  let b1 := y.val / 2
  ⟨(a0 * b0 + a1 * b1) % 2 + 2 * ((a0 * b1 + a1 * b0 + a1 * b1) % 2), by omega⟩

@[expose] def mul (x y : F4) : F4 := ⟨mulCode x.code y.code⟩

instance : Zero F4 := ⟨⟨0⟩⟩
instance : One F4 := ⟨⟨1⟩⟩
instance : Add F4 := ⟨add⟩
instance : Mul F4 := ⟨mul⟩
instance : Neg F4 := ⟨id⟩
instance : Sub F4 := ⟨add⟩
instance : Inv F4 := ⟨fun x => mul x x⟩
instance : Div F4 := ⟨fun x y => mul x (mul y y)⟩

@[expose] def ω : F4 := ⟨2⟩

theorem add_def (x y : F4) : x + y = add x y := rfl
theorem mul_def (x y : F4) : x * y = mul x y := rfl

instance : CommRing F4 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  neg_add_cancel := by decide
  mul_comm := by decide
  sub_eq_add_neg := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec
  npow := npowRec

instance : Field F4 where
  mul_inv_cancel := by decide
  inv_zero := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  div_eq_mul_inv := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

theorem card : Fintype.card F4 = 4 := by decide

theorem two_eq_zero : (2 : F4) = 0 := by decide

instance : CharP F4 2 := by
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  exact two_eq_zero

theorem sq_sq : ∀ x : F4, (x ^ 2) ^ 2 = x := by decide

end F4

noncomputable def F4.equivGaloisField : F4 ≃+* GaloisField 2 2 :=
  letI : Algebra (ZMod 2) F4 := ZMod.algebra F4 2
  (GaloisField.algEquivGaloisFieldOfFintype 2 2 (by rw [F4.card]; norm_num)).toRingEquiv

end CFSG.Fischer
