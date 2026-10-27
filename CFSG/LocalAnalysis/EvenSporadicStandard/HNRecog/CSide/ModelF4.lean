module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

@[ext] structure F4 where
  a : ZMod 2
  b : ZMod 2
  deriving DecidableEq

namespace F4

def equivProd : F4 ≃ ZMod 2 × ZMod 2 where
  toFun x := (x.a, x.b)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype F4 := Fintype.ofEquiv _ equivProd.symm

instance : Zero F4 := ⟨⟨0, 0⟩⟩
instance : One F4 := ⟨⟨1, 0⟩⟩
instance : Add F4 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg F4 := ⟨fun x => x⟩
instance : Mul F4 := ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

instance : CommRing F4 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide
  zero_mul := by decide
  mul_zero := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Inv F4 := ⟨fun x => x * x⟩

instance : Field F4 where
  mul_inv_cancel := by decide
  inv_zero := by decide
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  exists_pair_ne := ⟨0, 1, by decide⟩

def omega : F4 := ⟨0, 1⟩

theorem omega_sq_add : omega * omega + omega + 1 = 0 := by decide

def frob : F4 →+* F4 where
  toFun x := x * x
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

def tr (x : F4) : ZMod 2 := x.b

theorem card_eq : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr equivProd]
  decide

theorem natCast_eq (n : ℕ) : (n : F4) = ⟨(n : ZMod 2), 0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ, ih, Nat.cast_succ]
    rfl

instance : CharP F4 2 where
  cast_eq_zero_iff n := by
    rw [natCast_eq, ← CharP.cast_eq_zero_iff (ZMod 2) 2 n]
    constructor
    · intro h
      exact congrArg F4.a h
    · intro h
      rw [h]
      rfl

end F4

end CFSG.EvenSporadicStandard.HNRecog.CSide
