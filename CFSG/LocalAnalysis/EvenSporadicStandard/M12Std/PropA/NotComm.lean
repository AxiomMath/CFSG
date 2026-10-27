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

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

private lemma mem_sup_zpowers_eq_zpow_mul {G : Type*} [Group G] {x y : G} {J₁ : Subgroup G}
    (hxJ : ∀ j ∈ J₁, x * j = j * x) (hy : y ∈ zpowers x ⊔ J₁) :
    ∃ a : ℤ, ∃ j ∈ J₁, y = x ^ a * j := by
  have hxJc : ∀ j ∈ J₁, Commute x j := fun j hj => hxJ j hj
  rw [Subgroup.sup_eq_closure_mul] at hy
  refine Subgroup.closure_induction''
    (p := fun z _ => ∃ a : ℤ, ∃ j ∈ J₁, z = x ^ a * j) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨p, hp, j, hj, rfl⟩
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact ⟨a, j, hj, by rw [ha]⟩
  · rintro z ⟨p, hp, j, hj, rfl⟩
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hp
    refine ⟨-a, j⁻¹, J₁.inv_mem hj, ?_⟩
    rw [← ha, mul_inv_rev, ← zpow_neg x a]
    exact (hxJc j hj).symm.inv_left.zpow_right (-a)
  · exact ⟨0, 1, J₁.one_mem, by simp⟩
  · rintro p q _ _ ⟨a1, j1, hj1, rfl⟩ ⟨a2, j2, hj2, rfl⟩
    refine ⟨a1 + a2, j1 * j2, J₁.mul_mem hj1 hj2, ?_⟩
    calc (x ^ a1 * j1) * (x ^ a2 * j2)
        = x ^ a1 * (j1 * x ^ a2) * j2 := by group
      _ = x ^ a1 * (x ^ a2 * j1) * j2 := by rw [(hxJc j1 hj1).symm.zpow_right a2]
      _ = x ^ (a1 + a2) * (j1 * j2) := by rw [zpow_add x a1 a2]; group

theorem false_of_commutator_eq {G : Type*} [Group G] {x c y : G} {J₁ : Subgroup G}
    (hx1 : x ≠ 1) (hc : c * x = x * c) (hxJ : ∀ j ∈ J₁, x * j = j * x)
    (hZ : ∀ j ∈ J₁, (∀ j' ∈ J₁, j * j' = j' * j) → j = 1)
    (hcomm : J₁.map (MulAut.conj c).toMonoidHom ≠ J₁ →
      ∀ a ∈ J₁.map (MulAut.conj c).toMonoidHom, ∀ b ∈ J₁, a * b = b * a)
    (hy : y ∈ zpowers x ⊔ J₁) (hcy : c * y * c⁻¹ * y⁻¹ = x) : False := by
  obtain ⟨a, j, hj, hy_eq⟩ := mem_sup_zpowers_eq_zpow_mul hxJ hy
  have hcy' : c * y * c⁻¹ = x * y := by
    calc c * y * c⁻¹ = c * y * c⁻¹ * y⁻¹ * y := by group
      _ = x * y := by rw [hcy]
  rw [hy_eq] at hcy'
  have hc' : Commute c x := hc
  have hcxa : c * x ^ a = x ^ a * c := hc'.zpow_right a
  have h1 : c * (x ^ a * j) * c⁻¹ = x ^ a * (c * j * c⁻¹) := by
    calc c * (x ^ a * j) * c⁻¹
        = (c * x ^ a) * (j * c⁻¹) := by group
      _ = (x ^ a * c) * (j * c⁻¹) := by rw [hcxa]
      _ = x ^ a * (c * j * c⁻¹) := by group
  have h2 : x * (x ^ a * j) = x ^ a * (x * j) := by
    calc x * (x ^ a * j)
        = (x * x ^ a) * j := by group
      _ = (x ^ a * x) * j := by rw [(Commute.refl x).zpow_right a]
      _ = x ^ a * (x * j) := by group
  have hcj : c * j * c⁻¹ = x * j := by
    have key : x ^ a * (c * j * c⁻¹) = x ^ a * (x * j) := by
      rw [← h1, hcy', h2]
    exact mul_left_cancel key
  have hx_eq : x = (c * j * c⁻¹) * j⁻¹ := by
    rw [hcj]
    group
  by_cases hJJ : J₁.map (MulAut.conj c).toMonoidHom = J₁
  · have hu : c * j * c⁻¹ ∈ J₁.map (MulAut.conj c).toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨j, hj, by simp [MulAut.conj_apply]⟩
    have hxmem : x ∈ J₁ := by
      rw [hx_eq, ← hJJ]
      exact mul_mem hu (by rw [hJJ]; exact J₁.inv_mem hj)
    exact hx1 (hZ x hxmem hxJ)
  · have hu : c * j * c⁻¹ ∈ J₁.map (MulAut.conj c).toMonoidHom := by
      rw [Subgroup.mem_map]
      exact ⟨j, hj, by simp [MulAut.conj_apply]⟩
    have hu_comm : ∀ w ∈ J₁, (c * j * c⁻¹) * w = w * (c * j * c⁻¹) :=
      fun w hw => hcomm hJJ (c * j * c⁻¹) hu w hw
    have hv_comm : ∀ w ∈ J₁, j⁻¹ * w = w * j⁻¹ := by
      intro w hw
      have hxw : x * w = w * x := hxJ w hw
      rw [hx_eq] at hxw
      have h2 : (c * j * c⁻¹) * (j⁻¹ * w) = (c * j * c⁻¹) * (w * j⁻¹) := by
        calc (c * j * c⁻¹) * (j⁻¹ * w)
            = ((c * j * c⁻¹) * j⁻¹) * w := by group
          _ = w * ((c * j * c⁻¹) * j⁻¹) := hxw
          _ = (w * (c * j * c⁻¹)) * j⁻¹ := by group
          _ = ((c * j * c⁻¹) * w) * j⁻¹ := by rw [← hu_comm w hw]
          _ = (c * j * c⁻¹) * (w * j⁻¹) := by group
      exact mul_left_cancel h2
    have hv1 : j⁻¹ = 1 := hZ j⁻¹ (J₁.inv_mem hj) hv_comm
    have hj1 : j = 1 := inv_eq_one.mp hv1
    have hu1 : c * j * c⁻¹ = 1 := by rw [hj1]; group
    exact hx1 (by rw [hx_eq, hu1, hv1]; group)

end CFSG.EvenSporadicStandard.M12Std.PropA
