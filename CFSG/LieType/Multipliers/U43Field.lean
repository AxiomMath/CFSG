module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LieType.Multipliers.U43

@[ext]
structure F9 where
  re : ZMod 3
  im : ZMod 3

namespace F9

instance : DecidableEq F9 := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.im = b.im) F9.ext_iff.symm

instance : Fintype F9 :=
  Fintype.ofEquiv (ZMod 3 × ZMod 3)
    ⟨fun p => ⟨p.1, p.2⟩, fun a => (a.re, a.im), fun _ => rfl, fun _ => rfl⟩

instance : Zero F9 := ⟨⟨0, 0⟩⟩
instance : One F9 := ⟨⟨1, 0⟩⟩
instance : Add F9 := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Neg F9 := ⟨fun a => ⟨-a.re, -a.im⟩⟩
instance : Sub F9 := ⟨fun a b => ⟨a.re - b.re, a.im - b.im⟩⟩
instance : Mul F9 := ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩

private theorem zero_def : (0 : F9) = ⟨0, 0⟩ := rfl
private theorem one_def : (1 : F9) = ⟨1, 0⟩ := rfl
private theorem add_def (a b : F9) : a + b = ⟨a.re + b.re, a.im + b.im⟩ := rfl
private theorem neg_def (a : F9) : -a = ⟨-a.re, -a.im⟩ := rfl
private theorem sub_def (a b : F9) : a - b = ⟨a.re - b.re, a.im - b.im⟩ := rfl
private theorem mul_def (a b : F9) :
    a * b = ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩ := rfl

instance : CommRing F9 where
  add_assoc a b c := by ext <;> simp only [add_def] <;> ring
  zero_add a := by ext <;> simp only [add_def, zero_def] <;> ring
  add_zero a := by ext <;> simp only [add_def, zero_def] <;> ring
  add_comm a b := by ext <;> simp only [add_def] <;> ring
  sub_eq_add_neg a b := by ext <;> simp only [add_def, neg_def, sub_def] <;> ring
  neg_add_cancel a := by ext <;> simp only [add_def, neg_def, zero_def] <;> ring
  mul_assoc a b c := by ext <;> simp only [mul_def] <;> ring
  one_mul a := by ext <;> simp only [mul_def, one_def] <;> ring
  mul_one a := by ext <;> simp only [mul_def, one_def] <;> ring
  zero_mul a := by ext <;> simp only [mul_def, zero_def] <;> ring
  mul_zero a := by ext <;> simp only [mul_def, zero_def] <;> ring
  left_distrib a b c := by ext <;> simp only [mul_def, add_def] <;> ring
  right_distrib a b c := by ext <;> simp only [mul_def, add_def] <;> ring
  mul_comm a b := by ext <;> simp only [mul_def] <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Inv F9 := ⟨fun a => a * a * a * a * a * a * a⟩

theorem mul_inv_seven : ∀ a : F9, a ≠ 0 → a * a⁻¹ = 1 := by decide

instance : Field F9 where
  exists_pair_ne := ⟨0, 1, by decide⟩
  mul_inv_cancel := mul_inv_seven
  inv_zero := by decide
  nnqsmul := _
  qsmul := _

theorem card_eq : Fintype.card F9 = 9 := rfl

end F9

end CFSG.LieType.Multipliers.U43
