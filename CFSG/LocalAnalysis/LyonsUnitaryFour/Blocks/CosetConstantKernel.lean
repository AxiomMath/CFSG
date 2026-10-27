module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LyonsUnitaryFour

open scoped BigOperators

@[expose] noncomputable def subgroupAverage {L : Type*} [Group L] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ L V) (H : Subgroup L) [Fintype H] : Module.End ℂ V :=
  ((Nat.card H : ℂ)⁻¹) • ∑ h : H, ρ h

theorem mul_subgroupAverage {L : Type*} [Group L] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ L V) (H : Subgroup L) [Fintype H] (h : L) (hh : h ∈ H) :
    ρ h * subgroupAverage ρ H = subgroupAverage ρ H := by
  unfold subgroupAverage
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : H))
  intro k
  rw [← map_mul]
  rfl

theorem subgroupAverage_idempotent {L : Type*} [Group L] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ L V) (H : Subgroup L) [Fintype H] :
    IsIdempotentElem (subgroupAverage ρ H) := by
  have hne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  change subgroupAverage ρ H * subgroupAverage ρ H = subgroupAverage ρ H
  conv_lhs => arg 1; unfold subgroupAverage
  rw [smul_mul_assoc, Finset.sum_mul,
    Finset.sum_congr rfl (fun (h : H) _ => mul_subgroupAverage ρ H (h : L) h.property),
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem trace_mul_subgroupAverage {L : Type*} [Group L] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ L V) (H : Subgroup L) [Fintype H]
    (x : L) :
    LinearMap.trace ℂ V (ρ x * subgroupAverage ρ H) =
      (Nat.card H : ℂ)⁻¹ * ∑ h : H, ρ.character (x * h) := by
  unfold subgroupAverage
  rw [mul_smul_comm, map_smul, Finset.mul_sum, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  rw [← map_mul]
  rfl

theorem coset_constant_character_fixed_space_kernel {L : Type*} [Group L] [Finite L]
    (H P : Subgroup L) (_hPH : P ≤ Subgroup.normalizer (H : Set L))
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ L V) (hfix : ∀ v : V, (∀ x ∈ P, ρ x v = v) → v = 0)
    (hconst : ∀ x ∈ P, x ≠ 1 → ∀ h ∈ H, ρ.character (x * h) = ρ.character x) :
    H ≤ MonoidHom.ker ρ := by
  classical
  let := Fintype.ofFinite H
  let := Fintype.ofFinite P
  have hHne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hPne : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hP0 : subgroupAverage ρ P = 0 := by
    ext v
    apply hfix
    intro x hx
    have h := congrArg (fun f : Module.End ℂ V => f v) (mul_subgroupAverage ρ P x hx)
    simpa using h
  have htrP : (∑ x : P, ρ.character x) = 0 := by
    have h := congrArg (LinearMap.trace ℂ V) hP0
    unfold subgroupAverage at h
    rw [map_smul, map_sum, map_zero, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hPne)
  have htrPH : (∑ x : P, ∑ h : H, ρ.character (x * h)) = 0 := by
    have h := congrArg (LinearMap.trace ℂ V) (congrArg (· * subgroupAverage ρ H) hP0)
    simp only [zero_mul, map_zero] at h
    unfold subgroupAverage at h
    rw [smul_mul_assoc, Finset.sum_mul, map_smul, map_sum, smul_eq_mul] at h
    have h' := (mul_eq_zero.mp h).resolve_left (inv_ne_zero hPne)
    have hsum : (∑ x : P, LinearMap.trace ℂ V (ρ x * subgroupAverage ρ H)) =
        (Nat.card H : ℂ)⁻¹ * ∑ x : P, ∑ h : H, ρ.character (x * h) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => trace_mul_subgroupAverage ρ H x)
    unfold subgroupAverage at hsum
    rw [hsum] at h'
    exact (mul_eq_zero.mp h').resolve_left (inv_ne_zero hHne)
  have hsplit : ∀ f : P → ℂ, ∑ x : P, f x = f 1 + ∑ x ∈ Finset.univ.erase (1 : P), f x := by
    intro f
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
  have hcoset : ∀ x ∈ Finset.univ.erase (1 : P),
      (∑ h : H, ρ.character ((x : L) * h)) = (Nat.card H : ℂ) * ρ.character x := by
    intro x hx
    have hx1 : (x : L) ≠ 1 := by
      intro h
      apply (Finset.mem_erase.mp hx).1
      exact Subtype.ext h
    rw [Finset.sum_congr rfl (fun (h : H) _ => hconst (x : L) x.property hx1 (h : L) h.property),
      Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
  have htr1 : (∑ h : H, ρ.character (((1 : P) : L) * (h : L))) =
      (Nat.card H : ℂ) * LinearMap.trace ℂ V (subgroupAverage ρ H) := by
    have h := trace_mul_subgroupAverage ρ H 1
    rw [map_one, one_mul] at h
    rw [h, Subgroup.coe_one]
    field_simp
  rw [hsplit, htr1, Finset.sum_congr rfl hcoset, ← Finset.mul_sum] at htrPH
  rw [hsplit] at htrP
  have htrH : LinearMap.trace ℂ V (subgroupAverage ρ H) = ρ.character 1 := by
    have h1 : LinearMap.trace ℂ V (subgroupAverage ρ H) +
        ∑ x ∈ Finset.univ.erase (1 : P), ρ.character x = 0 := by
      have := htrPH
      rw [← mul_add] at this
      exact (mul_eq_zero.mp this).resolve_left hHne
    have h2 : ρ.character ((1 : P) : L) + ∑ x ∈ Finset.univ.erase (1 : P), ρ.character x = 0 :=
      htrP
    rw [Subgroup.coe_one] at h2
    linear_combination h1 - h2
  have hidem : IsIdempotentElem (1 - subgroupAverage ρ H) :=
    (subgroupAverage_idempotent ρ H).one_sub
  have htr0 : LinearMap.trace ℂ V (1 - subgroupAverage ρ H) = 0 := by
    rw [map_sub, htrH, LinearMap.trace_one, Representation.char_one]
    simp
  have heq : 1 - subgroupAverage ρ H = 0 :=
    LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hidem htr0
  have heH1 : subgroupAverage ρ H = 1 := (sub_eq_zero.mp heq).symm
  intro h hh
  rw [MonoidHom.mem_ker]
  have := mul_subgroupAverage ρ H h hh
  rw [heH1, mul_one] at this
  exact this

end CFSG.LyonsUnitaryFour
