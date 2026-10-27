module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElementsInputs
public import CFSG.Monster.B.Final.Basic
public import CFSG.Monster.B.Pinned.Primes.Program

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

section Elements


@[expose] noncomputable def b7EReg (k : ℕ) : NativeSporadic.B := runG (b7EProg ()) bA₁ bA₂ k

@[expose] noncomputable def a0B7 : NativeSporadic.B := b7EReg 2

@[expose] noncomputable def xB7 : NativeSporadic.B := b7EReg 5

@[expose] noncomputable def yB7 : NativeSporadic.B := b7EReg 7

@[expose] noncomputable def t1B7 : NativeSporadic.B := b7EReg 11

@[expose] noncomputable def t2B7 : NativeSporadic.B := b7EReg 6

@[expose] noncomputable def eB7 : NativeSporadic.B := b7EReg 16

end Elements

structure B7EParts (a x y t1 t2 e : NativeSporadic.B) : Prop where
  mul_self_a : a * a = 1
  ne_one_a : a ≠ 1
  rank_a : Matrix.rank (bMat a - 1) = 1860
  comm_a_x : a * x = x * a
  comm_a_y : a * y = y * a
  comm_a_t1 : a * t1 = t1 * a
  comm_a_t2 : a * t2 = t2 * a
  comm_a_e : a * e = e * a
  order_x : orderOf x = 7
  order_y : orderOf y = 5
  comm_x_y : x * y = y * x
  mul_self_t1 : t1 * t1 = 1
  ne_one_t1 : t1 ≠ 1
  mul_self_t2 : t2 * t2 = 1
  ne_one_t2 : t2 ≠ 1
  ne_t1_t2 : t1 ≠ t2
  comm_t1_t2 : t1 * t2 = t2 * t1
  comm_t1_x : t1 * x = x * t1
  comm_t2_x : t2 * x = x * t2
  rank_t1 : Matrix.rank (bMat t1 - 1) = 1860
  rank_t2 : Matrix.rank (bMat t2 - 1) = 1860
  rank_t1_t2 : Matrix.rank (bMat (t1 * t2) - 1) = 2048
  rank_a_t1 : Matrix.rank (bMat (a * t1) - 1) = 2158
  ne_t1_a : t1 ≠ a
  ne_t2_a : t2 ≠ a
  order_e : orderOf e = 3
  comm_e_x : e * x = x * e
  comm_e_t1 : e * t1 = t1 * e
  w_pow_six : (t1 * e) ^ 6 = 1
  w_pow_three : (t1 * e) ^ 3 = t1
  w_sq_ne_one : (t1 * e) * (t1 * e) ≠ 1
  w_sq_ne_a : (t1 * e) * (t1 * e) ≠ a
  comm_t1_y : t1 * y ≠ y * t1
  comm_t1_y_a : t1 * y ≠ a * y * t1

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
