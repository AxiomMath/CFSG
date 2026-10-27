module

public import CFSG.LieType.Chevalley.E6Three.StabilizerFour

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E6Three.StabilizerN6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.Chevalley.E6Three.ModelKernel CFSG.LieType.Chevalley.E6Three.StabilizerFour

structure N6 where
  b0 : ℕ
  b1 : ℕ
  b2 : ℕ
  b3 : ℕ
  b4 : ℕ
  b5 : ℕ

@[expose] def N6.toFun (b : N6) (k : Fin Tag.E6.rank) : ZMod 3 :=
  match k.val with
  | 0 => b.b0
  | 1 => b.b1
  | 2 => b.b2
  | 3 => b.b3
  | 4 => b.b4
  | _ => b.b5

@[expose] def N6.tri (i : Fin Tag.E6.rank) (b : N6) : N6 :=
  match i.val with
  | 0 => { b with b0 := 2 * b.b0 % 3, b2 := (b.b2 + b.b0) % 3 }
  | 1 => { b with b1 := 2 * b.b1 % 3, b3 := (b.b3 + b.b1) % 3 }
  | 2 => { b with b2 := 2 * b.b2 % 3, b0 := (b.b0 + b.b2) % 3, b3 := (b.b3 + b.b2) % 3 }
  | 3 =>
    { b with
      b3 := 2 * b.b3 % 3, b1 := (b.b1 + b.b3) % 3, b2 := (b.b2 + b.b3) % 3,
      b4 := (b.b4 + b.b3) % 3 }
  | 4 => { b with b4 := 2 * b.b4 % 3, b3 := (b.b3 + b.b4) % 3, b5 := (b.b5 + b.b4) % 3 }
  | _ => { b with b5 := 2 * b.b5 % 3, b4 := (b.b4 + b.b5) % 3 }

@[expose] def N6.tact (ω : List (Fin Tag.E6.rank)) (b : N6) : N6 := ω.foldr N6.tri b

@[expose] def N6.key (b c : N6) : ℕ :=
  b.b0 % 3 + 3 * (b.b1 % 3 + 3 * (b.b2 % 3 + 3 * (b.b3 % 3 + 3 * (b.b4 % 3 + 3 * (b.b5 % 3 +
    3 * (c.b0 % 3 + 3 * (c.b1 % 3 + 3 * (c.b2 % 3 + 3 * (c.b3 % 3 + 3 * (c.b4 % 3 +
      3 * (c.b5 % 3)))))))))))

theorem sub_two_mul_self (x : ZMod 3) : x - 2 * x = 2 * x := by
  revert x
  decide

@[expose] def triReflect6 (i : Fin 6) (b : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  fun j => b j - (Tag.cartanE 6 i j : ZMod 3) * b i

theorem triReflect6_toFun (i : Fin 6) (b : N6) :
    triReflect6 i b.toFun = (b.tri i).toFun := by
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [triReflect6, N6.tri, N6.toFun, Tag.cartanE, ZMod.natCast_mod, sub_two_mul_self]

theorem triAct_toFun (ω : List (Fin Tag.E6.rank)) (b : N6) :
    triAct ω b.toFun = (b.tact ω).toFun := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change triReflect6 i (triAct ω b.toFun) = _
    rw [ih]
    exact triReflect6_toFun i (b.tact ω)

theorem pairKey_toFun (b c : N6) : pairKey b.toFun c.toFun = N6.key b c := rfl

theorem positionBasis_three_zero : positionBasis 3 0 = N6.toFun ⟨1, 2, 1, 0, 0, 0⟩ := by
  decide +kernel

theorem positionBasis_three_one : positionBasis 3 1 = N6.toFun ⟨0, 0, 0, 1, 0, 0⟩ := by
  decide +kernel

end CFSG.LieType.Chevalley.E6Three.StabilizerN6
