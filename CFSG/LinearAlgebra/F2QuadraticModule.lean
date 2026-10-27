module

public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LocalRing.Basic

open Polynomial Module

public section

namespace CFSG.LinearAlgebra.F2Quadratic

theorem irreducible_quad : Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp)
  intro x hx
  rw [IsRoot.def] at hx
  simp only [eval_add, eval_pow, eval_X, eval_one] at hx
  revert hx
  revert x
  decide

abbrev GF4 : Type := AdjoinRoot (X ^ 2 + X + 1 : (ZMod 2)[X])

local instance : Fact (Irreducible (X ^ 2 + X + 1 : (ZMod 2)[X])) := ⟨irreducible_quad⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (T : Module.End (ZMod 2) V)

theorem aeval_quad (hT : T * T + T + 1 = 0) :
    aeval T (X ^ 2 + X + 1 : (ZMod 2)[X]) = 0 := by
  simp [pow_two, hT]

theorem isTorsionBy_quad (hT : T * T + T + 1 = 0) :
    IsTorsionBy (ZMod 2)[X] (AEval' T) (X ^ 2 + X + 1 : (ZMod 2)[X]) := by
  intro m
  apply (AEval.of (ZMod 2) V T).symm.injective
  rw [AEval.of_symm_smul, aeval_quad T hT]
  simp

theorem scalarTower_GF4 (hT : T * T + T + 1 = 0) :
    letI : Module GF4 (AEval' T) := (isTorsionBy_quad T hT).module
    IsScalarTower (ZMod 2) GF4 (AEval' T) := by
  let : Module GF4 (AEval' T) := (isTorsionBy_quad T hT).module
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  have h : algebraMap (ZMod 2) GF4 r =
      Ideal.Quotient.mk (Ideal.span {(X ^ 2 + X + 1 : (ZMod 2)[X])}) (C r) := rfl
  rw [h]
  exact (IsTorsionBy.mk_smul (isTorsionBy_quad T hT) (C r) m).trans (AEval.C_smul T r m)

theorem finrank_eq_two_mul (hT : T * T + T + 1 = 0) [Module.Finite (ZMod 2) V] :
    letI : Module GF4 (AEval' T) := (isTorsionBy_quad T hT).module
    Module.finrank (ZMod 2) V = 2 * Module.finrank GF4 (AEval' T) := by
  let : Module GF4 (AEval' T) := (isTorsionBy_quad T hT).module
  have := scalarTower_GF4 T hT
  have h1 := Module.finrank_mul_finrank (ZMod 2) GF4 (AEval' T)
  have h2 : Module.finrank (ZMod 2) GF4 = 2 := by
    have hf : (X ^ 2 + X + 1 : (ZMod 2)[X]) ≠ 0 := irreducible_quad.ne_zero
    have hdeg : (X ^ 2 + X + 1 : (ZMod 2)[X]).natDegree = 2 := by compute_degree!
    rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have h3 : Module.finrank (ZMod 2) (AEval' T) = Module.finrank (ZMod 2) V :=
    (LinearEquiv.finrank_eq (AEval.of (ZMod 2) V T)).symm
  rw [← h3, ← h1, h2]

theorem exists_equiv_of_quadratic {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    [Module.Finite (ZMod 2) V] [Module.Finite (ZMod 2) V'] (T' : Module.End (ZMod 2) V')
    (hT : T * T + T + 1 = 0) (hT' : T' * T' + T' + 1 = 0)
    (hdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) V') :
    ∃ e : V ≃ₗ[ZMod 2] V', ∀ v, e (T v) = T' (e v) := by
  let : Module GF4 (AEval' T) := (isTorsionBy_quad T hT).module
  let : Module GF4 (AEval' T') := (isTorsionBy_quad T' hT').module
  have := scalarTower_GF4 T hT
  have := scalarTower_GF4 T' hT'
  have h1 : Module.finrank GF4 (AEval' T) = Module.finrank GF4 (AEval' T') := by
    have h2 := finrank_eq_two_mul T hT
    have h3 := finrank_eq_two_mul T' hT'
    omega
  have : Module.Finite GF4 (AEval' T) := Module.Finite.of_restrictScalars_finite (ZMod 2) GF4 _
  have : Module.Finite GF4 (AEval' T') := Module.Finite.of_restrictScalars_finite (ZMod 2) GF4 _
  let e₀ : AEval' T ≃ₗ[GF4] AEval' T' := LinearEquiv.ofFinrankEq _ _ h1
  refine ⟨(AEval.of (ZMod 2) V T).trans ((e₀.restrictScalars (ZMod 2)).trans
    (AEval.of (ZMod 2) V' T').symm), fun v => ?_⟩
  have hX : ∀ m : AEval' T, e₀ ((X : (ZMod 2)[X]) • m) = (X : (ZMod 2)[X]) • e₀ m := by
    intro m
    have h4 : (X : (ZMod 2)[X]) • m =
        (AdjoinRoot.mk (X ^ 2 + X + 1 : (ZMod 2)[X]) X : GF4) • m := rfl
    have h5 : (X : (ZMod 2)[X]) • e₀ m =
        (AdjoinRoot.mk (X ^ 2 + X + 1 : (ZMod 2)[X]) X : GF4) • e₀ m := rfl
    rw [h4, h5, map_smul]
  have h6 := hX (AEval.of (ZMod 2) V T v)
  rw [AEval.X_smul_of] at h6
  show (AEval.of (ZMod 2) V' T').symm (e₀ (AEval.of (ZMod 2) V T (T v))) =
    T' ((AEval.of (ZMod 2) V' T').symm (e₀ (AEval.of (ZMod 2) V T v)))
  have h7 : T • v = T v := rfl
  rw [h7] at h6
  rw [h6, AEval.of_symm_X_smul]
  rfl

end CFSG.LinearAlgebra.F2Quadratic
