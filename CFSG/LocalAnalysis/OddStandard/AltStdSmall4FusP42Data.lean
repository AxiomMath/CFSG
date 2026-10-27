module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fin.VecNotation

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.P42

open Equiv

@[expose] def bxor (k l : Fin 16) : Fin 16 :=
  ⟨k.val ^^^ l.val, by
    have h := Nat.xor_lt_two_pow (n := 4) (x := k.val) (y := l.val) (by simpa using k.2)
      (by simpa using l.2)
    simpa using h⟩

@[expose] def bFun (k : Fin 16) (x : Fin 9) : Fin 9 :=
  if h : x.val < 4 then
    ⟨x.val ^^^ (k.val % 4), by
      have h1 := Nat.xor_lt_two_pow (n := 2) (x := x.val) (y := k.val % 4) (by simpa using h)
        (by simp; omega)
      simp at h1
      omega⟩
  else if h' : x.val < 8 then
    ⟨x.val ^^^ (k.val / 4), by
      have h1 := Nat.xor_lt_two_pow (n := 3) (x := x.val) (y := k.val / 4) (by simpa using h')
        (by simp; omega)
      simp at h1
      omega⟩
  else x

theorem bFun_involutive (k : Fin 16) : Function.Involutive (bFun k) := by
  intro x
  revert k x
  decide

@[expose] def bEl (k : Fin 16) : Perm (Fin 9) :=
  Function.Involutive.toPerm (bFun k) (bFun_involutive k)

@[expose] def bGen : Fin 4 → Perm (Fin 9) :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7]

@[expose] def bIdx (σ : Perm (Fin 9)) : Fin 16 :=
  ⟨(σ 0).val % 4 + 4 * ((σ 4).val % 4), by omega⟩

@[expose] def normB (σ : Perm (Fin 9)) : Bool :=
  decide (σ 8 = 8) && decide (∀ j : Fin 4, σ * bGen j * σ⁻¹ = bEl (bIdx (σ * bGen j * σ⁻¹))) &&
    decide (Perm.sign σ = 1)

@[expose] def centB (σ : Perm (Fin 9)) : Bool :=
  decide (σ 8 = 8) && decide (∀ j : Fin 4, σ * bGen j = bGen j * σ) && decide (Perm.sign σ = 1)

@[expose] def p42Check (_ : Unit := ()) : Bool :=
  (Finset.univ.filter fun σ : Perm (Fin 9) => normB σ = true).card == 576 &&
    (Finset.univ.filter fun σ : Perm (Fin 9) => centB σ = true).card == 16

end CFSG.OddStandard.AltStdSmall4.Fus.P42
