module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoMatrixCentralizer
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Topology.Sheaves.Init

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBLinearTwo

open Matrix

theorem scalarGL_injective (K : Type*) [Field K] :
    Function.Injective (GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GeneralLinearGroup (Fin 2) K) := by
  intro a b hab
  apply Units.ext
  simpa [GeneralLinearGroup.scalar] using
    congrArg (fun A : GeneralLinearGroup (Fin 2) K => A.val 0 0) hab

@[expose] def projectiveCentralizerLift {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) : Subgroup (GeneralLinearGroup (Fin 2) K) :=
  (Subgroup.centralizer {ProjGenLinGroup.mk A}).comap ProjGenLinGroup.mk

theorem exists_scalarDisplacement {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (B : projectiveCentralizerLift A) :
    ∃ c : Kˣ, A * B.val * GeneralLinearGroup.scalar (Fin 2) c = B.val * A := by
  apply ProjGenLinGroup.mk_eq_mk_iff.mp
  simpa only [map_mul] using
    (Subgroup.mem_centralizer_singleton_iff.mp B.property).symm

@[expose] def scalarDisplacement {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (B : projectiveCentralizerLift A) : Kˣ :=
  (exists_scalarDisplacement A B).choose

theorem scalarDisplacement_spec {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (B : projectiveCentralizerLift A) :
    A * B.val * GeneralLinearGroup.scalar (Fin 2) (scalarDisplacement A B) = B.val * A :=
  (exists_scalarDisplacement A B).choose_spec

theorem scalarDisplacement_unique {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (B : projectiveCentralizerLift A) (c : Kˣ)
    (hc : A * B.val * GeneralLinearGroup.scalar (Fin 2) c = B.val * A) :
    scalarDisplacement A B = c :=
  scalarGL_injective K (mul_left_cancel ((scalarDisplacement_spec A B).trans hc.symm))

@[expose] def scalarDisplacementHom {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) : projectiveCentralizerLift A →* Kˣ where
  toFun := scalarDisplacement A
  map_one' := scalarDisplacement_unique A 1 1 (by simp)
  map_mul' B C := by
    apply scalarDisplacement_unique
    change A * (B.val * C.val) * GeneralLinearGroup.scalar (Fin 2)
      (scalarDisplacement A B * scalarDisplacement A C) = B.val * C.val * A
    rw [map_mul]
    calc
      A * (B.val * C.val) *
          (GeneralLinearGroup.scalar (Fin 2) (scalarDisplacement A B) *
            GeneralLinearGroup.scalar (Fin 2) (scalarDisplacement A C)) =
        (A * B.val * GeneralLinearGroup.scalar (Fin 2) (scalarDisplacement A B)) *
          C.val * GeneralLinearGroup.scalar (Fin 2) (scalarDisplacement A C) := by
            simp only [mul_assoc]
            rw [← GeneralLinearGroup.scalar_commute _ C.val]
            rw [GeneralLinearGroup.scalar_commute _ C.val]
            rw [← mul_assoc C.val, ← GeneralLinearGroup.scalar_commute _ C.val,
              mul_assoc]
      _ = (B.val * A) * C.val *
          GeneralLinearGroup.scalar (Fin 2) (scalarDisplacement A C) := by
            rw [scalarDisplacement_spec]
      _ = B.val * (A * C.val *
          GeneralLinearGroup.scalar (Fin 2) (scalarDisplacement A C)) := by group
      _ = B.val * C.val * A := by rw [scalarDisplacement_spec]; group

theorem scalarDisplacement_eq_one_iff {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (B : projectiveCentralizerLift A) :
    scalarDisplacement A B = 1 ↔ B.val * A = A * B.val := by
  constructor
  · intro h
    simpa only [h, map_one, mul_one] using (scalarDisplacement_spec A B).symm
  · intro h
    exact scalarDisplacement_unique A B 1 (by simpa using h.symm)

theorem matrix_square_central_of_projective_square {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) :
    A ^ 2 ∈ Subgroup.center (GeneralLinearGroup (Fin 2) K) := by
  apply ProjGenLinGroup.mk_eq_one.mp
  simpa only [map_pow] using hsquare

theorem scalarDisplacement_square_eq_one {K : Type*} [Field K]
    (A : GeneralLinearGroup (Fin 2) K) (hsquare : ProjGenLinGroup.mk A ^ 2 = 1)
    (B : projectiveCentralizerLift A) : scalarDisplacement A B ^ 2 = 1 := by
  let S := GeneralLinearGroup.scalar (Fin 2) (scalarDisplacement A B)
  have hBA : B.val * A = A * B.val * S := (scalarDisplacement_spec A B).symm
  have hAS : S * A = A * S := GeneralLinearGroup.scalar_commute _ _
  have hcentral := Subgroup.mem_center_iff.mp
    (matrix_square_central_of_projective_square A hsquare) B.val
  have hcancel : (A ^ 2 * B.val) * (S ^ 2) = A ^ 2 * B.val := by
    calc
      (A ^ 2 * B.val) * (S ^ 2) = A * (A * B.val * S) * S := by
        simp only [pow_two, mul_assoc]
      _ = A * (B.val * A) * S := by rw [← hBA]
      _ = (A * B.val * S) * A := by simp only [mul_assoc]; rw [hAS]
      _ = B.val * A * A := by rw [← hBA]
      _ = A ^ 2 * B.val := by simpa only [pow_two, mul_assoc] using hcentral
  have hS : S ^ 2 = 1 := mul_left_cancel (by simpa only [mul_one] using hcancel)
  apply scalarGL_injective K
  simpa only [map_pow, map_one, S] using hS

end CFSG.ComponentClassification.CatalogueBLinearTwo
