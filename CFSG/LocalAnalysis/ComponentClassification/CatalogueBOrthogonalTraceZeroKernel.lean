module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

theorem traceZeroOrthogonalAction_scalar (c : Kˣ) :
    traceZeroOrthogonalAction (GeneralLinearGroup.scalar (Fin 2) c) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change (GeneralLinearGroup.scalar (Fin 2) c).val * X.val *
    (GeneralLinearGroup.scalar (Fin 2) c)⁻¹.val = X.val
  have hc : (GeneralLinearGroup.scalar (Fin 2) c).val * X.val =
      X.val * (GeneralLinearGroup.scalar (Fin 2) c).val := by
    rw [GeneralLinearGroup.coe_scalar]
    exact Matrix.scalar_comm (c : K) (Commute.all _) X.val
  rw [hc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem traceZeroOrthogonalAction_commutes_of_eq_one (A : GL (Fin 2) K)
    (hA : traceZeroOrthogonalAction A = 1) (X : traceZeroSubmodule K) :
    A.val * X.val = X.val * A.val := by
  have h : A.val * X.val * A⁻¹.val = X.val :=
    congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) =>
      (g.val X).val) hA
  have h' := congrArg (fun Z : Matrix (Fin 2) (Fin 2) K => Z * A.val) h
  simpa only [Matrix.mul_assoc, A.inv_mul, Matrix.mul_one] using h'

theorem traceZeroOrthogonalAction_ker :
    (traceZeroOrthogonalAction (K := K)).ker = Subgroup.center (GL (Fin 2) K) := by
  ext A
  constructor
  · intro hA
    have hE := traceZeroOrthogonalAction_commutes_of_eq_one A hA
      (traceZeroCoordinates K ![0, 1, 0])
    have hF := traceZeroOrthogonalAction_commutes_of_eq_one A hA
      (traceZeroCoordinates K ![0, 0, 1])
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hE
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hF
    have hdiag := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hE
    have hc : A.val 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, traceZeroCoordinates] using h10.symm
    have hb : A.val 0 1 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, traceZeroCoordinates] using h01
    have hd : A.val 0 0 = A.val 1 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, traceZeroCoordinates] using hdiag
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    refine ⟨A.val 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, hb, hc, hd]
  · intro hA
    rw [GeneralLinearGroup.center_eq_range_scalar] at hA
    obtain ⟨c, rfl⟩ := hA
    exact traceZeroOrthogonalAction_scalar c

theorem traceZeroOrthogonalAction_eq_one_iff (A : GL (Fin 2) K) :
    traceZeroOrthogonalAction A = 1 ↔
      ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin 2) c = A := by
  rw [← MonoidHom.mem_ker, traceZeroOrthogonalAction_ker,
    GeneralLinearGroup.center_eq_range_scalar]
  rfl

@[expose] def traceZeroBracket (X Y : traceZeroSubmodule K) : traceZeroSubmodule K :=
  ⟨X.val * Y.val - Y.val * X.val, by
    change (X.val * Y.val - Y.val * X.val).trace = 0
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]⟩

theorem traceZeroConjugation_bracket (A : GL (Fin 2) K) (X Y : traceZeroSubmodule K) :
    traceZeroConjugation A (traceZeroBracket X Y) =
      traceZeroBracket (traceZeroConjugation A X) (traceZeroConjugation A Y) := by
  apply Subtype.ext
  change A.val * (X.val * Y.val - Y.val * X.val) * A⁻¹.val =
    (A.val * X.val * A⁻¹.val) * (A.val * Y.val * A⁻¹.val) -
      (A.val * Y.val * A⁻¹.val) * (A.val * X.val * A⁻¹.val)
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc A⁻¹.val A.val, A.inv_mul, Matrix.one_mul]

theorem traceZeroBracket_neg_neg (X Y : traceZeroSubmodule K) :
    traceZeroBracket (-X) (-Y) = traceZeroBracket X Y := by
  apply Subtype.ext
  change (-X.val) * (-Y.val) - (-Y.val) * (-X.val) =
    X.val * Y.val - Y.val * X.val
  rw [neg_mul_neg, neg_mul_neg]

theorem traceZeroBracket_basis :
    traceZeroBracket (traceZeroCoordinates K ![0, 1, 0])
      (traceZeroCoordinates K ![0, 0, 1]) = traceZeroCoordinates K ![1, 0, 0] := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceZeroBracket, traceZeroCoordinates]

theorem traceZeroOrthogonalAction_ne_neg (h2 : (2 : K) ≠ 0) (A : GL (Fin 2) K) :
    traceZeroOrthogonalAction A ≠ QuadraticMap.negOrthogonal (traceZeroForm K) := by
  intro hA
  have hneg (X : traceZeroSubmodule K) : traceZeroConjugation A X = -X := by
    have h := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K) =>
      g.val X) hA
    rw [QuadraticMap.coe_negOrthogonal] at h
    exact h
  have h := traceZeroConjugation_bracket A
    (traceZeroCoordinates K ![0, 1, 0]) (traceZeroCoordinates K ![0, 0, 1])
  rw [traceZeroBracket_basis, hneg, hneg, hneg, traceZeroBracket_neg_neg,
    traceZeroBracket_basis] at h
  have hentry : -(1 : K) = 1 := congrArg (fun X : traceZeroSubmodule K => X.val 0 0) h
  apply h2
  linear_combination -hentry

end CFSG.ComponentClassification.CatalogueBOrthogonal
