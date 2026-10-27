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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem two_dvd_natCard [FiniteDimensional (ZMod 2) W] [Nontrivial W] : 2 ∣ Nat.card W := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Fintype W := Fintype.ofFinite W
  have hpos : 0 < finrank (ZMod 2) W := Module.finrank_pos
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  exact dvd_pow_self 2 hpos.ne'

theorem exists_fixed_ne_zero [Finite G] (hG : IsPGroup 2 G) (σ : G →* (W ≃ₗ[ZMod 2] W))
    [FiniteDimensional (ZMod 2) W] [Nontrivial W] : ∃ w : W, w ≠ 0 ∧ ∀ g, σ g w = w := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  let _ : MulAction G W :=
    { smul := fun g v => σ g v
      one_smul := fun v => by
        change σ 1 v = v
        rw [map_one]
        rfl
      mul_smul := fun a b v => by
        change σ (a * b) v = σ a (σ b v)
        rw [map_mul]
        rfl }
  have h0 : (0 : W) ∈ MulAction.fixedPoints G W := fun g => map_zero (σ g)
  obtain ⟨b, hb, hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point W
    two_dvd_natCard h0
  exact ⟨b, hne.symm, fun g => hb g⟩

theorem sum_translate_smul [Fintype G] (σ : G →* (W ≃ₗ[ZMod 2] W)) (w : W) (c : G → ZMod 2)
    (h : G) : ∑ g, c (h⁻¹ * g) • σ g w = σ h (∑ g, c g • σ g w) := by
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
  change c (h⁻¹ * g) • σ g w = σ h (c (h⁻¹ * g) • σ (h⁻¹ * g) w)
  rw [map_smul, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem sum_apply_eq_zero_of_relation [Fintype G] (hG : IsPGroup 2 G)
    (σ : G →* (W ≃ₗ[ZMod 2] W)) (w : W) {c : G → ZMod 2} (hc : ∑ g, c g • σ g w = 0)
    {g₀ : G} (hg₀ : c g₀ ≠ 0) : ∑ g, σ g w = 0 := by
  classical
  let L : (G → ZMod 2) →ₗ[ZMod 2] W := Fintype.linearCombination (ZMod 2) fun g => σ g w
  have hL : ∀ c : G → ZMod 2, L c = ∑ g, c g • σ g w := fun c =>
    Fintype.linearCombination_apply (ZMod 2) _ c
  generalize hK : LinearMap.ker L = K
  have hmemK : ∀ c, c ∈ K ↔ ∑ g, c g • σ g w = 0 := fun c => by
    rw [← hK, LinearMap.mem_ker, hL]
  have hmem : ∀ (h : G) (c : K), (fun g => (c : G → ZMod 2) (h⁻¹ * g)) ∈ K := by
    intro h c
    rw [hmemK, sum_translate_smul σ w _ h, (hmemK c).mp c.2, map_zero]
  let _ : MulAction G K :=
    { smul := fun h c => ⟨fun g => (c : G → ZMod 2) (h⁻¹ * g), hmem h c⟩
      one_smul := fun c => Subtype.ext (funext fun g => by
        change (c : G → ZMod 2) (1⁻¹ * g) = (c : G → ZMod 2) g
        rw [inv_one, one_mul])
      mul_smul := fun a b c => Subtype.ext (funext fun g => by
        change (c : G → ZMod 2) ((a * b)⁻¹ * g) = (c : G → ZMod 2) (b⁻¹ * (a⁻¹ * g))
        rw [mul_inv_rev, mul_assoc]) }
  have : Finite K := Finite.of_injective (fun c : K => (c : G → ZMod 2)) Subtype.val_injective
  have hcK : c ∈ K := (hmemK c).mpr hc
  have : Nontrivial K := ⟨⟨⟨c, hcK⟩, 0, fun h => hg₀ (congrFun (congrArg Subtype.val h) g₀)⟩⟩
  have h0 : (0 : K) ∈ MulAction.fixedPoints G K := fun h => Subtype.ext (funext fun g => rfl)
  obtain ⟨b, hb, hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point K
    two_dvd_natCard h0
  have hconst : ∀ g, (b : G → ZMod 2) g = (b : G → ZMod 2) 1 := by
    intro g
    have := congrFun (congrArg Subtype.val (hb g)) g
    change (b : G → ZMod 2) (g⁻¹ * g) = (b : G → ZMod 2) g at this
    rw [inv_mul_cancel] at this
    exact this.symm
  have hb1 : (b : G → ZMod 2) 1 = 1 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) ((b : G → ZMod 2) 1) with h1 | h1
    · refine absurd (Subtype.ext (funext fun g => ?_)) hne
      rw [hconst g, h1]
      rfl
    · exact h1
  have hbK := (hmemK b).mp b.2
  simpa [hconst, hb1] using hbK

theorem sum_apply_eq_zero [Fintype G] (hG : IsPGroup 2 G) (σ : G →* (W ≃ₗ[ZMod 2] W))
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W < Fintype.card G) (w : W) :
    ∑ g, σ g w = 0 := by
  by_contra hs
  have hli : LinearIndependent (ZMod 2) fun g => σ g w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc g₀
    by_contra hg₀
    exact hs (sum_apply_eq_zero_of_relation hG σ w hc hg₀)
  have := hli.fintype_card_le_finrank
  omega

end CFSG.LargeExtraspecial.SL4Mod
