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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.ClassicalInvolution.Q3

open Matrix Module

section Eigen

variable {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isCompl_eigenspaces {g : Matrix ι ι E} {μ : E} (h2μ : (2 : E) * μ ≠ 0)
    (hg : g * g = (μ * μ) • (1 : Matrix ι ι E)) :
    IsCompl (Module.End.eigenspace (Matrix.toLin' g) μ)
      (Module.End.eigenspace (Matrix.toLin' g) (-μ)) := by
  have hgg : ∀ v, g *ᵥ (g *ᵥ v) = (μ * μ) • v := fun v => by
    rw [Matrix.mulVec_mulVec, hg, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro v h1 h2
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at h1 h2
    have h3 : ((2 : E) * μ) • v = 0 := by
      have : ((2 : E) * μ) • v = μ • v - (-μ) • v := by module
      rw [this, ← h1, ← h2, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left h2μ
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.mpr ⟨((2 : E) * μ)⁻¹ • (g *ᵥ v + μ • v), ?_,
      ((2 : E) * μ)⁻¹ • (μ • v - g *ᵥ v), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_smul,
        Matrix.mulVec_add, Matrix.mulVec_smul, hgg]
      module
    · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_smul,
        Matrix.mulVec_sub, Matrix.mulVec_smul, hgg]
      module
    · have h2 : ((2 : E) * μ)⁻¹ * (2 * μ) = 1 := inv_mul_cancel₀ h2μ
      calc ((2 : E) * μ)⁻¹ • (g *ᵥ v + μ • v) + ((2 : E) * μ)⁻¹ • (μ • v - g *ᵥ v)
          = (((2 : E) * μ)⁻¹ * (2 * μ)) • v := by module
        _ = v := by rw [h2, one_smul]

theorem exists_eigenbasis_matrix {g : Matrix ι ι E} {μ : E} (h2μ : (2 : E) * μ ≠ 0)
    (hg : g * g = (μ * μ) • (1 : Matrix ι ι E)) :
    ∃ (a b : ℕ) (Q : Matrix ι (Fin a ⊕ Fin b) E) (Q' : Matrix (Fin a ⊕ Fin b) ι E),
      Q * Q' = 1 ∧ Q' * Q = 1 ∧
        g * Q = Q * Matrix.fromBlocks (μ • (1 : Matrix (Fin a) (Fin a) E)) 0 0
          ((-μ) • (1 : Matrix (Fin b) (Fin b) E)) := by
  have hcompl := isCompl_eigenspaces h2μ hg
  set Vp := Module.End.eigenspace (Matrix.toLin' g) μ with hVp
  set Vm := Module.End.eigenspace (Matrix.toLin' g) (-μ) with hVm
  set bp := Module.finBasis E Vp with hbp
  set bq := Module.finBasis E Vm with hbq
  set Bs : Module.Basis (Fin (finrank E Vp) ⊕ Fin (finrank E Vm)) E (ι → E) :=
    (bp.prod bq).map (Submodule.prodEquivOfIsCompl Vp Vm hcompl) with hBs
  refine ⟨finrank E Vp, finrank E Vm, (Pi.basisFun E ι).toMatrix Bs,
    Bs.toMatrix (Pi.basisFun E ι), Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, ?_⟩
  have hcol : ∀ c, g *ᵥ (Bs c) =
      (Sum.elim (fun _ => μ) (fun _ => -μ) c) • Bs c := by
    rintro (i | i)
    · have : Bs (Sum.inl i) = (bp i : ι → E) := by
        simp [hBs]
      rw [this]
      have := (bp i).2
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
      simpa using this
    · have : Bs (Sum.inr i) = (bq i : ι → E) := by
        simp [hBs]
      rw [this]
      have := (bq i).2
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at this
      simpa using this
  ext r c
  rcases c with i | i
  · have h1 : (g * (Pi.basisFun E ι).toMatrix Bs) r (Sum.inl i) =
        μ * ((Pi.basisFun E ι).toMatrix Bs) r (Sum.inl i) := by
      have := congrFun (hcol (Sum.inl i)) r
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply] using this
    rw [h1, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [Matrix.one_apply]
    first | done | ring
  · have h1 : (g * (Pi.basisFun E ι).toMatrix Bs) r (Sum.inr i) =
        (-μ) * ((Pi.basisFun E ι).toMatrix Bs) r (Sum.inr i) := by
      have := congrFun (hcol (Sum.inr i)) r
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply] using this
    rw [h1, Matrix.mul_apply, Fintype.sum_sum_type]
    simp [Matrix.one_apply]
    first | done | ring

end Eigen

end CFSG.ClassicalInvolution.Q3
