module

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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open scoped MatrixGroups
open Matrix

variable (F : Type) [Field F]

@[expose] def sc : Subgroup (GL (Fin 3) F) := (Matrix.GeneralLinearGroup.scalar (Fin 3)).range

section Scalar

variable {F}

abbrev scal (c : Fˣ) : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) c

theorem mem_sc_iff {g : GL (Fin 3) F} : g ∈ sc F ↔ ∃ c : Fˣ, g = scal c := by
  simp only [sc, MonoidHom.mem_range, eq_comm]

theorem scal_pow (c : Fˣ) (n : ℕ) : (scal (c ^ n) : GL (Fin 3) F) = scal c ^ n :=
  (Matrix.GeneralLinearGroup.scalar (Fin 3)).map_pow c n

theorem scal_mul (c d : Fˣ) : (scal (c * d) : GL (Fin 3) F) = scal c * scal d :=
  (Matrix.GeneralLinearGroup.scalar (Fin 3)).map_mul c d

theorem scal_one : (scal (1 : Fˣ) : GL (Fin 3) F) = 1 :=
  (Matrix.GeneralLinearGroup.scalar (Fin 3)).map_one

theorem scal_inv (c : Fˣ) : (scal c⁻¹ : GL (Fin 3) F) = (scal c)⁻¹ :=
  (Matrix.GeneralLinearGroup.scalar (Fin 3)).map_inv c

theorem scal_mem_sc (c : Fˣ) : scal c ∈ sc F := mem_sc_iff.mpr ⟨c, rfl⟩

theorem coe_scal (c : Fˣ) :
    ((scal c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) (c : F) :=
  Matrix.GeneralLinearGroup.coe_scalar c

theorem sc_mem_center {g : GL (Fin 3) F} (hg : g ∈ sc F) : g ∈ Subgroup.center (GL (Fin 3) F) := by
  obtain ⟨c, rfl⟩ := mem_sc_iff.mp hg
  rw [Subgroup.mem_center_iff]
  intro h
  exact (Matrix.GeneralLinearGroup.scalar_commute c h).symm

end Scalar

@[expose] def diagGL (a b c : Fˣ) : GL (Fin 3) F where
  val := Matrix.diagonal ![(a : F), b, c]
  inv := Matrix.diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext k
    fin_cases k <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext k
    fin_cases k <;> simp

theorem diagGL_mul (a b c a' b' c' : Fˣ) :
    diagGL F a b c * diagGL F a' b' c' = diagGL F (a * a') (b * b') (c * c') := by
  apply Units.ext
  simp only [diagGL, Units.val_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  ext k
  fin_cases k <;> simp

theorem diagGL_inv (a b c : Fˣ) : (diagGL F a b c)⁻¹ = diagGL F a⁻¹ b⁻¹ c⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [diagGL_mul]
  apply Units.ext
  simp only [diagGL]
  rw [Units.val_one, ← Matrix.diagonal_one]
  congr 1
  ext k
  fin_cases k <;> simp

@[expose] def torusThree : Subgroup (GL (Fin 3) F) where
  carrier := {g | ∃ a b c : Fˣ, a ^ 3 = b ^ 3 ∧ b ^ 3 = c ^ 3 ∧ g = diagGL F a b c}
  mul_mem' := by
    rintro _ _ ⟨a, b, c, h1, h2, rfl⟩ ⟨a', b', c', h1', h2', rfl⟩
    refine ⟨a * a', b * b', c * c', ?_, ?_, (diagGL_mul F ..)⟩
    · rw [mul_pow, mul_pow, h1, h1']
    · rw [mul_pow, mul_pow, h2, h2']
  one_mem' := ⟨1, 1, 1, by simp, by simp, by
    apply Units.ext
    simp only [diagGL, Units.val_one]
    rw [← Matrix.diagonal_one]
    congr 1
    ext k
    fin_cases k <;> simp⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, h1, h2, rfl⟩
    refine ⟨a⁻¹, b⁻¹, c⁻¹, ?_, ?_, diagGL_inv F ..⟩
    · rw [inv_pow, inv_pow, h1]
    · rw [inv_pow, inv_pow, h2]

@[expose] def monomGL (lam : Fˣ) : GL (Fin 3) F where
  val := !![0, 0, (lam : F); 1, 0, 0; 0, 1, 0]
  inv := !![0, 1, 0; 0, 0, 1; ((lam⁻¹ : Fˣ) : F), 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def heisenbergThree (lam ω : Fˣ) : Subgroup (GL (Fin 3) F) :=
  Subgroup.closure (↑(sc F) ∪ {monomGL F lam, diagGL F 1 ω (ω ^ 2)})

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
