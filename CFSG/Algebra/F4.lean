module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Algebra.Field.Defs

public section

namespace CFSG

structure F4 where
  a : ZMod 2
  b : ZMod 2
deriving DecidableEq, Fintype, Repr, Inhabited

namespace F4

theorem ext {x y : F4} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; simp_all

theorem ext_iff {x y : F4} : x = y ↔ x.a = y.a ∧ x.b = y.b :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext h.1 h.2⟩

attribute [ext] ext

instance : Zero F4 := ⟨⟨0, 0⟩⟩

instance : One F4 := ⟨⟨1, 0⟩⟩

instance : Add F4 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩

instance : Mul F4 :=
  ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

instance : Neg F4 := ⟨id⟩

instance : Sub F4 := ⟨fun x y => x + y⟩

instance : Inv F4 := ⟨fun x => if x = 0 then 0 else x * x⟩

instance : Div F4 := ⟨fun x y => x * y⁻¹⟩

instance : NatCast F4 := ⟨Nat.unaryCast⟩

instance : IntCast F4 := ⟨Int.castDef⟩

instance : Pow F4 Nat := ⟨fun x n => npowRec n x⟩

instance : Pow F4 Int := ⟨fun x n => zpowRec npowRec n x⟩

@[simp] theorem zero_def : (0 : F4) = ⟨0, 0⟩ := rfl

@[simp] theorem one_def : (1 : F4) = ⟨1, 0⟩ := rfl

@[simp] theorem add_def (x y : F4) : x + y = ⟨x.a + y.a, x.b + y.b⟩ := rfl

@[simp] theorem mul_def (x y : F4) :
    x * y = ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩ := rfl

@[simp] theorem neg_def (x : F4) : -x = x := rfl

theorem sub_def (x y : F4) : x - y = x + y := rfl

@[simp] theorem inv_def (x : F4) : x⁻¹ = if x = 0 then 0 else x * x := rfl

theorem div_def (x y : F4) : x / y = x * y⁻¹ := rfl

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

@[simp] theorem natCast_def (n : ℕ) : (n : F4) = ⟨n, 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.cast_succ, ih]
      ext <;> simp [add_comm]

@[simp] theorem intCast_def (n : ℤ) : (n : F4) = ⟨n, 0⟩ := by
  cases n with
  | ofNat n => simpa using natCast_def n
  | negSucc n =>
      rw [Int.cast_negSucc, natCast_def]
      ext <;> simp [add_comm]

instance : Field F4 where
  mul_inv_cancel := by decide
  inv_zero := by decide
  exists_pair_ne := ⟨0, 1, by decide⟩
  div_eq_mul_inv := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

@[simp] theorem pow_nat_def (x : F4) (n : ℕ) : x ^ n = npowRec n x := rfl

@[simp] theorem pow_int_def (x : F4) (n : ℤ) : x ^ n = zpowRec npowRec n x := rfl

@[expose] def omega : F4 := ⟨0, 1⟩

@[simp] theorem omega_def : omega = ⟨0, 1⟩ := rfl

theorem omega_sq' : omega ^ 2 = omega + 1 := by decide

theorem omega_sq : omega * omega = omega + 1 := by decide

theorem omega_cube : omega ^ 3 = 1 := by decide

theorem omega_ne_zero : omega ≠ 0 := by decide

theorem omega_ne_one : omega ≠ 1 := by decide

theorem omega_sq_add_omega_add_one : omega ^ 2 + omega + 1 = 0 := by decide

theorem eq_add_mul_omega (x : F4) : x = ⟨x.a, 0⟩ + ⟨x.b, 0⟩ * omega := by
  ext <;> simp

theorem exists_eq_add_mul_omega (x : F4) :
    ∃ a b : ZMod 2, x = ⟨a, 0⟩ + ⟨b, 0⟩ * omega :=
  ⟨x.a, x.b, eq_add_mul_omega x⟩

theorem card : Fintype.card F4 = 4 := by decide

theorem two_eq_zero : (2 : F4) = 0 := by decide

instance instCharP : CharP F4 2 := by
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  exact two_eq_zero

theorem add_self (x : F4) : x + x = 0 := by
  revert x
  decide

end F4

end CFSG
