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
public import Mathlib.LinearAlgebra.Center
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.LinearAlgebra

open Matrix

theorem projective_linear_kernel {K : Type*} [Field K] {n : ℕ} (A : GL (Fin n) K) :
    (∀ L : Submodule K (Fin n → K), Module.finrank K L = 1 →
        L.map (Matrix.toLin' (A : Matrix (Fin n) (Fin n) K)) = L) ↔
      ∃ c : Kˣ, A = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  constructor
  · intro h
    have hcol : ∀ v : Fin n → K,
        ¬ LinearIndependent K ![v, Matrix.toLin' (A : Matrix _ _ K) v] := by
      intro v hv
      by_cases hv0 : v = 0
      · exact hv.ne_zero 0 (by simp [hv0])
      have hL := h (K ∙ v) (finrank_span_singleton hv0)
      have hmem : Matrix.toLin' (A : Matrix _ _ K) v ∈ K ∙ v := by
        rw [← hL]
        exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self v)
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
      rw [LinearIndependent.pair_iff] at hv
      have := hv a (-1) (by rw [← ha]; simp)
      exact absurd this.2 (by norm_num)
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hcol
    have hA : (A : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) a := by
      apply Matrix.toLin'.injective
      rw [ha]
      ext v i
      simp [Matrix.toLin'_apply, Matrix.scalar_apply, Pi.single_apply]
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exact ⟨1, Subsingleton.elim _ _⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      have hdet := (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit
      rw [hA, map_zero, Matrix.det_zero] at hdet
      exact not_isUnit_zero hdet
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar, hA]
    rfl
  · rintro ⟨c, rfl⟩ L _
    ext x
    simp only [Submodule.mem_map, Matrix.GeneralLinearGroup.coe_scalar]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [Matrix.toLin'_apply, Matrix.scalar_apply] using L.smul_mem (c : K) hy
    · intro hx
      refine ⟨(c⁻¹ : Kˣ) • x, L.smul_mem _ hx, ?_⟩
      simp [Matrix.toLin'_apply, Matrix.scalar_apply, Units.smul_def, smul_smul]

end CFSG.LinearAlgebra
