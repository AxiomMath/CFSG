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

namespace CFSG.TwoRankLowerBound.Helpers

theorem mem_zpowers_of_injective_iff {source target : Type*} [Group source] [Group target]
    (homomorphism : source →* target) (hinjective : Function.Injective homomorphism)
    (element root : source) :
    homomorphism element ∈ Subgroup.zpowers (homomorphism root) ↔
      element ∈ Subgroup.zpowers root := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · intro hroot
    obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp hroot
    exact ⟨exponent, hinjective (by simpa only [map_zpow] using hexponent)⟩
  · rintro ⟨exponent, rfl⟩
    exact ⟨exponent, (map_zpow homomorphism root exponent).symm⟩

theorem odd_kernel_root_projection_iff {G : Type*} [Group G] [Finite G]
    (complement : Subgroup G) (htwo : IsPGroup 2 complement)
    (projection : G →* complement)
    (hidentity : ∀ element : complement, projection element = element)
    (hodd : Odd (Nat.card projection.ker)) (element : complement)
    (hcentralizes : ∀ member ∈ projection.ker, Commute member (element : G))
    (root : G) :
    (element : G) ∈ Subgroup.zpowers root ↔
      element ∈ Subgroup.zpowers (projection root) := by
  constructor
  · rintro ⟨exponent, hexponent⟩
    change root ^ exponent = (element : G) at hexponent
    apply Subgroup.mem_zpowers_iff.mpr
    exact ⟨exponent, by rw [← map_zpow, hexponent, hidentity]⟩
  · intro hroot
    obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp hroot
    let kernelMember := root ^ exponent * (element : G)⁻¹
    have hkernelMember : kernelMember ∈ projection.ker := by
      change projection (root ^ exponent * (element : G)⁻¹) = 1
      rw [map_mul, map_zpow, map_inv, hexponent, hidentity, mul_inv_cancel]
    have hcommute := hcentralizes kernelMember hkernelMember
    have hfactor : root ^ exponent = kernelMember * (element : G) := by
      simp [kernelMember]
    have hkernelPow : kernelMember ^ Nat.card projection.ker = 1 := by
      exact congrArg Subtype.val
        (pow_card_eq_one' (x := (⟨kernelMember, hkernelMember⟩ : projection.ker)))
    have hpower : (element : G) ^ Nat.card projection.ker ∈ Subgroup.zpowers root := by
      rw [← one_mul ((element : G) ^ Nat.card projection.ker), ← hkernelPow,
        ← hcommute.mul_pow, ← hfactor]
      exact (Subgroup.zpowers root).pow_mem (Subgroup.zpow_mem_zpowers root exponent) _
    have hcoprime := (htwo.orderOf_coprime (Nat.coprime_two_left.mpr hodd) element).symm
    obtain ⟨powerExponent, hpowerExponent⟩ := exists_pow_eq_self_of_coprime hcoprime
    have hpowerExponent : ((element : G) ^ Nat.card projection.ker) ^ powerExponent = element :=
      congrArg Subtype.val hpowerExponent
    rw [← hpowerExponent]
    exact (Subgroup.zpowers root).pow_mem hpower powerExponent

end CFSG.TwoRankLowerBound.Helpers
