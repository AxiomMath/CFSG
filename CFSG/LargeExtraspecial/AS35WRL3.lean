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
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

namespace CFSG.LargeExtraspecial

open Subgroup Matrix

namespace AS35W

variable (F : Type) [Field F]

@[expose] def rootL3 (t : F) : Matrix (Fin 3) (Fin 3) F := !![1, t, 0; 0, 1, 0; 0, 0, 1]

@[expose] def diagL3 : Matrix (Fin 3) (Fin 3) F := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

variable {F}

theorem rootL3_add (s t : F) : rootL3 F (s + t) = rootL3 F s * rootL3 F t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootL3, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem rootL3_zero : rootL3 F 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootL3]

theorem det_rootL3 (t : F) : (rootL3 F t).det = 1 := by
  simp [rootL3, Matrix.det_fin_three]

theorem det_diagL3 : (diagL3 F).det = 1 := by
  simp [diagL3, Matrix.det_fin_three]

theorem rootL3_comm (t : F) : rootL3 F t * diagL3 F = diagL3 F * rootL3 F t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootL3, diagL3, Matrix.mul_apply, Fin.sum_univ_three]

theorem diagL3_mul_self : diagL3 F * diagL3 F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagL3, Matrix.mul_apply, Fin.sum_univ_three]

variable (F)

@[expose] def slInvL3 : Matrix.SpecialLinearGroup (Fin 3) F := ⟨diagL3 F, det_diagL3⟩

@[expose] def psl3Inv : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F :=
  QuotientGroup.mk (slInvL3 F)

variable {F}

theorem orderOf_psl3Inv (h2 : (2 : F) ≠ 0) : orderOf (psl3Inv F) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [psl3Inv, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have h1 : slInvL3 F ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, sq]
      exact diagL3_mul_self
    rw [h1]
    exact one_mem _
  · intro h1
    rw [psl3Inv, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h1
    obtain ⟨r, -, hr⟩ := h1
    have h00 := congrFun (congrFun hr 0) 0
    have h22 := congrFun (congrFun hr 2) 2
    simp [slInvL3, diagL3] at h00 h22
    apply h2
    linear_combination h00 - h22

theorem card_dvd_card_centralizer_psl3Inv [Finite F] :
    Nat.card F ∣ Nat.card (centralizer
      ({psl3Inv F} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))) := by
  let φ : Multiplicative F →* Matrix.SpecialLinearGroup (Fin 3) F :=
    { toFun := fun a => ⟨rootL3 F (Multiplicative.toAdd a), det_rootL3 _⟩
      map_one' := Subtype.ext rootL3_zero
      map_mul' := fun a b => Subtype.ext (rootL3_add _ _) }
  let ψ := (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) F))).comp φ
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hc : φ a ∈ center (Matrix.SpecialLinearGroup (Fin 3) F) :=
      (QuotientGroup.eq_one_iff _).1 ha
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hc
    obtain ⟨r, -, hr⟩ := hc
    have h01 := congrFun (congrFun hr 0) 1
    simp [φ, rootL3] at h01
    exact h01.symm
  have hle : ψ.range ≤
      centralizer ({psl3Inv F} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) := by
    rintro _ ⟨a, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change (QuotientGroup.mk (φ a * slInvL3 F) : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) =
      QuotientGroup.mk (slInvL3 F * φ a)
    congr 1
    exact Subtype.ext (rootL3_comm _)
  have hcard : Nat.card ψ.range = Nat.card F := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv]
    rfl
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

end AS35W

end CFSG.LargeExtraspecial
