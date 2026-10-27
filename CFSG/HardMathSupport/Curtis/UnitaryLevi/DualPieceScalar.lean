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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem dual_piece_scalar {B : V →ₛₗ[σ] V →ₗ[K] K} (g : LinearMap.GeneralLinearGroup K V)
    (hiso : ∀ v w, B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w)
    {F F' : Submodule K V}
    (hF'inv : ∀ v ∈ F', ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ F')
    (c : K) (hc : ∀ v ∈ F', (g : Module.End K V) v - c • v ∈ F) :
    ∀ w ∈ F.orthogonalBilin B, (g : Module.End K V) w - (σ c)⁻¹ • w ∈ F'.orthogonalBilin B := by
  intro w hw
  rw [Submodule.mem_orthogonalBilin] at hw ⊢
  intro v hv
  set u : V := ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v with hu
  have hgu : (g : Module.End K V) u = v := by
    rw [hu]
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
    rfl
  have hu' : u ∈ F' := hF'inv v hv
  have h1 : B v ((g : Module.End K V) w) = B u w := by
    rw [← hiso u w, hgu]
  have h2 : B u w = (σ c)⁻¹ * B v w := by
    by_cases hc0 : c = 0
    · have hvF : ∀ x ∈ F', x ∈ F := by
        intro x hx
        have hy := hF'inv x hx
        have h0 := hc _ hy
        have e : (g : Module.End K V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) :
            Module.End K V) x) = x := by
          rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
          rfl
        rwa [e, hc0, zero_smul, sub_zero] at h0
      rw [hw u (hvF u hu'), hc0, map_zero, inv_zero, zero_mul]
    · have h3 : u - c⁻¹ • v ∈ F := by
        have := F.smul_mem (-c⁻¹) (hc u hu')
        rw [hgu] at this
        convert this using 1
        simp only [smul_sub, smul_smul, neg_mul, neg_smul, inv_mul_cancel₀ hc0, one_smul]
        abel
      have h4 : u = c⁻¹ • v + (u - c⁻¹ • v) := by abel
      rw [h4, map_add, LinearMap.add_apply, hw _ h3, add_zero, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, map_inv₀]
  rw [map_sub, map_smul, h1, h2, smul_eq_mul]
  ring

end CFSG.HardMathSupport.Curtis.UnitaryLevi
