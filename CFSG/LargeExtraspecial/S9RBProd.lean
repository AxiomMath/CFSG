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

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup

variable {M : Type*} [Group M]

def prodSub (A B : Subgroup M)
    (hBA : ∀ a ∈ A, ∀ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') : Subgroup M where
  carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
  mul_mem' := by
    rintro _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    obtain ⟨a', ha', b', hb', e⟩ := hBA a₂ ha₂ b₁ hb₁
    exact ⟨a₁ * a', A.mul_mem ha₁ ha', b' * b₂, B.mul_mem hb' hb₂, by
      rw [mul_assoc a₁ b₁, ← mul_assoc b₁, e]; group⟩
  one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨a', ha', b', hb', e⟩ := hBA a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
    exact ⟨a', ha', b', hb', by rw [mul_inv_rev, e]⟩

theorem le_prodSub_left {A B : Subgroup M}
    (hBA : ∀ a ∈ A, ∀ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') : A ≤ prodSub A B hBA :=
  fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩

theorem le_prodSub_right {A B : Subgroup M}
    (hBA : ∀ a ∈ A, ∀ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') : B ≤ prodSub A B hBA :=
  fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩

section Comm

variable {t : M} {A B : Subgroup M}
  (hAc : ∀ a ∈ A, ∀ a' ∈ A, Commute a a') (hBc : ∀ b ∈ B, ∀ b' ∈ B, Commute b b')
  (htA : t ∈ A) (htB : t ∈ B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ zpowers t)

include hAB in
theorem exists_mul_comm (a : M) (ha : a ∈ A) (b : M) (hb : b ∈ B) :
    ∃ c ∈ zpowers t, b * a = c * (a * b) :=
  ⟨(a * b * a⁻¹ * b⁻¹)⁻¹, inv_mem (hAB a ha b hb), by group⟩

include hAB htA in
theorem prod_comm_of (a : M) (ha : a ∈ A) (b : M) (hb : b ∈ B) :
    ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b' := by
  obtain ⟨c, hc, e⟩ := exists_mul_comm hAB a ha b hb
  have hcA : c ∈ A := (zpowers_le.mpr htA) hc
  exact ⟨c * a, A.mul_mem hcA ha, b, hb, by rw [e, mul_assoc]⟩

include hAc hBc htA htB in
theorem commute_of_mem_zpowers {c : M} (hc : c ∈ zpowers t) {x : M} (hx : x ∈ A ∨ x ∈ B) :
    Commute c x := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  rcases hx with hx | hx
  · exact (hAc t htA x hx).zpow_left k
  · exact (hBc t htB x hx).zpow_left k

include hAc hBc htA htB in
theorem commute_t_of_mem_prodSub
    (hBA : ∀ a ∈ A, ∀ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') {x : M}
    (hx : x ∈ prodSub A B hBA) : Commute x t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact (hAc a ha t htA).mul_left (hBc b hb t htB)

include hAc hBc htA htB hAB in
theorem comm_mem_zpowers_of_mem_prodSub
    (hBA : ∀ a ∈ A, ∀ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') {x y : M}
    (hx : x ∈ prodSub A B hBA) (hy : y ∈ prodSub A B hBA) :
    x * y * x⁻¹ * y⁻¹ ∈ zpowers t := by
  obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
  obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
  obtain ⟨c₁, hc₁, e₁⟩ := exists_mul_comm hAB a₂ ha₂ b₁ hb₁
  obtain ⟨c₂, hc₂, e₂⟩ := exists_mul_comm hAB a₁ ha₁ b₂ hb₂
  have k₁ : Commute c₁ a₁ := commute_of_mem_zpowers hAc hBc htA htB hc₁ (Or.inl ha₁)
  have k₂ : Commute c₂ a₂ := commute_of_mem_zpowers hAc hBc htA htB hc₂ (Or.inl ha₂)
  have hxy : a₁ * b₁ * (a₂ * b₂) = c₁ * (a₁ * a₂ * (b₁ * b₂)) := by
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (c₁ * (a₂ * b₁)) * b₂ := by rw [e₁]
      _ = (a₁ * c₁) * (a₂ * b₁ * b₂) := by group
      _ = (c₁ * a₁) * (a₂ * b₁ * b₂) := by rw [← k₁.eq]
      _ = c₁ * (a₁ * a₂ * (b₁ * b₂)) := by group
  have hyx : a₂ * b₂ * (a₁ * b₁) = c₂ * (a₁ * a₂ * (b₁ * b₂)) := by
    calc a₂ * b₂ * (a₁ * b₁) = a₂ * (b₂ * a₁) * b₁ := by group
      _ = a₂ * (c₂ * (a₁ * b₂)) * b₁ := by rw [e₂]
      _ = (a₂ * c₂) * (a₁ * (b₂ * b₁)) := by group
      _ = (c₂ * a₂) * (a₁ * (b₁ * b₂)) := by rw [← k₂.eq, (hBc b₂ hb₂ b₁ hb₁).eq]
      _ = c₂ * ((a₂ * a₁) * (b₁ * b₂)) := by group
      _ = c₂ * (a₁ * a₂ * (b₁ * b₂)) := by rw [(hAc a₂ ha₂ a₁ ha₁).eq]
  have e : a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹ =
      (a₁ * b₁ * (a₂ * b₂)) * (a₂ * b₂ * (a₁ * b₁))⁻¹ := by group
  rw [e, hxy, hyx]
  have e' : c₁ * (a₁ * a₂ * (b₁ * b₂)) * (c₂ * (a₁ * a₂ * (b₁ * b₂)))⁻¹ = c₁ * c₂⁻¹ := by
    group
  rw [e']
  exact mul_mem hc₁ (inv_mem hc₂)

include hAc hBc htA htB hAB in
theorem mul_self_mem_zpowers_of_mem_prodSub (hA2 : ∀ a ∈ A, a * a = 1)
    (hB2 : ∀ b ∈ B, b * b = 1)
    (hBA : ∀ a ∈ A, ∀ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') {x : M}
    (hx : x ∈ prodSub A B hBA) : x * x ∈ zpowers t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨c, hc, e⟩ := exists_mul_comm hAB a ha b hb
  have k : Commute c a := commute_of_mem_zpowers hAc hBc htA htB hc (Or.inl ha)
  have h : a * b * (a * b) = c := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (c * (a * b)) * b := by rw [e]
      _ = (a * c) * a * (b * b) := by group
      _ = c * (a * a) * (b * b) := by rw [← k.eq]; group
      _ = c := by rw [hA2 a ha, hB2 b hb]; group
  rw [h]
  exact hc

end Comm

theorem conj_mem_prodSub {A B : Subgroup M}
    (hBA : ∀ a ∈ A, ∀ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') {τ : M}
    (hτA : ∀ a ∈ A, τ * a * τ⁻¹ ∈ A) (hτB : ∀ b ∈ B, τ * b * τ⁻¹ ∈ B) {x : M}
    (hx : x ∈ prodSub A B hBA) : τ * x * τ⁻¹ ∈ prodSub A B hBA := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨_, hτA a ha, _, hτB b hb, by group⟩

theorem prodSub_le {A B X : Subgroup M}
    (hBA : ∀ a ∈ A, ∀ b ∈ B, ∃ a' ∈ A, ∃ b' ∈ B, b * a = a' * b') (hA : A ≤ X) (hB : B ≤ X) :
    prodSub A B hBA ≤ X := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact X.mul_mem (hA ha) (hB hb)

end CFSG.LargeExtraspecial.S9.RB
