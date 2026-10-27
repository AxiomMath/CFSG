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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace GorensteinWalter.Support

private lemma isThreeCycle_sq_mul_of_involution_support_inter_card_one
    {α : Type*} [Fintype α] [DecidableEq α] {σ τ : Equiv.Perm α}
    (hσSq : σ ^ 2 = 1) (hτSq : τ ^ 2 = 1)
    (hInter : (σ.support ∩ τ.support).card = 1) :
    Equiv.Perm.IsThreeCycle ((σ * τ) ^ 2) := by
  obtain ⟨x, hxInter⟩ := Finset.card_eq_one.mp hInter
  have hxBoth : x ∈ σ.support ∩ τ.support := by
    rw [hxInter]
    simp
  have hxσ : x ∈ σ.support := Finset.mem_inter.mp hxBoth |>.1
  have hxτ : x ∈ τ.support := Finset.mem_inter.mp hxBoth |>.2
  have hσσ (y : α) : σ (σ y) = y := by
    have h := congrArg (fun f : Equiv.Perm α ↦ f y) hσSq
    simpa [pow_two] using h
  have hττ (y : α) : τ (τ y) = y := by
    have h := congrArg (fun f : Equiv.Perm α ↦ f y) hτSq
    simpa [pow_two] using h
  have hUnique {y : α} (hyσ : y ∈ σ.support) (hyτ : y ∈ τ.support) : y = x := by
    have hy : y ∈ σ.support ∩ τ.support := Finset.mem_inter.mpr ⟨hyσ, hyτ⟩
    rw [hxInter] at hy
    simpa using hy
  let a := σ x
  let b := τ x
  have haσ : a ∈ σ.support := by
    exact Equiv.Perm.apply_mem_support.mpr hxσ
  have hbτ : b ∈ τ.support := by
    exact Equiv.Perm.apply_mem_support.mpr hxτ
  have hax : a ≠ x := Equiv.Perm.mem_support.mp hxσ
  have hbx : b ≠ x := Equiv.Perm.mem_support.mp hxτ
  have haτ : a ∉ τ.support := by
    intro haτ
    exact hax (hUnique haσ haτ)
  have hbσ : b ∉ σ.support := by
    intro hbσ
    exact hbx (hUnique hbσ hbτ)
  have hτa : τ a = a := Equiv.Perm.notMem_support.mp haτ
  have hσb : σ b = b := Equiv.Perm.notMem_support.mp hbσ
  have hab : a ≠ b := by
    intro hab
    apply hax
    apply hUnique haσ
    simpa [hab] using hbτ
  let κ := (σ * τ) ^ 2
  have hκx : κ x = a := by
    simp [κ, pow_two, a, b, hσb, hττ]
  have hκa : κ a = b := by
    simp [κ, pow_two, a, b, hτa, hσσ, hσb]
  have hκb : κ b = x := by
    simp [κ, pow_two, a, b, hττ, hτa, hσσ]
  have hκfix {y : α} (hyx : y ≠ x) (hya : y ≠ a) (hyb : y ≠ b) : κ y = y := by
    by_cases hyσ : y ∈ σ.support
    · have hyτ : y ∉ τ.support := by
        intro hyτ
        exact hyx (hUnique hyσ hyτ)
      have hτy : τ y = y := Equiv.Perm.notMem_support.mp hyτ
      have hστ : σ y ∉ τ.support := by
        intro hστ
        have hσyx : σ y = x :=
          hUnique (Equiv.Perm.apply_mem_support.mpr hyσ) hστ
        apply hya
        calc
          y = σ (σ y) := (hσσ y).symm
          _ = σ x := congrArg σ hσyx
          _ = a := rfl
      have hτσ : τ (σ y) = σ y := Equiv.Perm.notMem_support.mp hστ
      simp [κ, pow_two, hτy, hτσ, hσσ]
    · have hσy : σ y = y := Equiv.Perm.notMem_support.mp hyσ
      by_cases hyτ : y ∈ τ.support
      · have hτσ : τ y ∉ σ.support := by
          intro hτσ
          have hτyx : τ y = x :=
            hUnique hτσ (Equiv.Perm.apply_mem_support.mpr hyτ)
          apply hyb
          calc
            y = τ (τ y) := (hττ y).symm
            _ = τ x := congrArg τ hτyx
            _ = b := rfl
        have hστ : σ (τ y) = τ y := Equiv.Perm.notMem_support.mp hτσ
        simp [κ, pow_two, hσy, hστ, hττ]
      · have hτy : τ y = y := Equiv.Perm.notMem_support.mp hyτ
        simp [κ, pow_two, hσy, hτy]
  have hκSupport : κ.support = {x, a, b} := by
    ext y
    rw [Equiv.Perm.mem_support]
    by_cases hyx : y = x
    · subst y
      simp [hκx, hax]
    by_cases hya : y = a
    · subst y
      simp [hκa, hab, hab.symm, hax]
    by_cases hyb : y = b
    · subst y
      simp [hκb, hbx, hbx.symm, hya]
    simp [hyx, hya, hyb, hκfix hyx hya hyb]
  apply card_support_eq_three_iff.mp
  rw [show (σ * τ) ^ 2 = κ from rfl, hκSupport]
  simp [hax, hbx, hab, Ne.symm]

lemma subgroup_eq_alternatingGroup_of_involution_support_inter_card_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (H : Subgroup (Equiv.Perm α)) (hPrimitive : MulAction.IsPreprimitive H α)
    (hAlternating : H ≤ alternatingGroup α) {σ τ : Equiv.Perm α}
    (hσMem : σ ∈ H) (hτMem : τ ∈ H)
    (hσSq : σ ^ 2 = 1) (hτSq : τ ^ 2 = 1)
    (hInter : (σ.support ∩ τ.support).card = 1) :
    H = alternatingGroup α := by
  apply le_antisymm hAlternating
  apply Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    hPrimitive
    (isThreeCycle_sq_mul_of_involution_support_inter_card_one hσSq hτSq hInter)
  exact H.pow_mem (H.mul_mem hσMem hτMem) 2

end GorensteinWalter.Support

end CFSG
