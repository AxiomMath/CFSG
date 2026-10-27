module

public import CFSG.LinearAlgebra.BinaryReflectionNormalizer

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Module QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)

variable {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]

theorem zmod2_mul_self (a : ZMod 2) : a * a = a := by
  revert a
  decide

theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod2_vec_neg (x : Y) : -x = x :=
  neg_eq_of_add_eq_zero_left (zmod2_vec_add_self x)

theorem q_add (q : QuadraticForm (ZMod 2) Y) (x y : Y) : q (x + y) = q x + q y + polar q x y :=
  QuadraticMap.map_add (⇑q) x y

theorem linearIndependent_pair_of_polar (q : QuadraticForm (ZMod 2) Y) {u w x : Y}
    (hu : u ≠ 0) (hxu : polar q x u = 0) (hxw : polar q x w = 1) :
    LinearIndependent (ZMod 2) ![u, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (polar q x) hst
  rw [polar_add_right, polar_smul_right, polar_smul_right, hxu, hxw, QuadraticMap.polar_zero_right,
    smul_zero, zero_add, smul_eq_mul, mul_one] at h1
  subst h1
  rw [zero_smul, add_zero] at hst
  exact ⟨(smul_eq_zero.1 hst).resolve_right hu, rfl⟩

theorem finrank_span_pair {u w : Y} (h : LinearIndependent (ZMod 2) ![u, w]) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {u, w}) = 2 := by
  have := finrank_span_eq_card h
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Fintype.card_fin] at this

variable (q : QuadraticForm (ZMod 2) Y)

variable {q}

end CFSG.LinearAlgebra.SteinbergBQ

