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
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
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

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

variable {G : Type*} [Group G]

theorem mem_sup_of_commutes {K K' : Subgroup G} (h : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) {x : G}
    (hx : x ∈ K ⊔ K') : ∃ k ∈ K, ∃ k' ∈ K', x = k * k' := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, K'.one_mem, by simp⟩
    · exact ⟨1, K.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k₁, hk₁, k₁', hk₁', rfl⟩ := hx
    obtain ⟨k₂, hk₂, k₂', hk₂', rfl⟩ := hy
    refine ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, k₁' * k₂', K'.mul_mem hk₁' hk₂', ?_⟩
    have h1 : k₁' * k₂ = k₂ * k₁' := (h k₂ hk₂ k₁' hk₁').symm
    calc k₁ * k₁' * (k₂ * k₂') = k₁ * (k₁' * k₂) * k₂' := by group
      _ = k₁ * (k₂ * k₁') * k₂' := by rw [h1]
      _ = k₁ * k₂ * (k₁' * k₂') := by group
  | inv x _ hx =>
    obtain ⟨k, hk, k', hk', rfl⟩ := hx
    refine ⟨k⁻¹, K.inv_mem hk, k'⁻¹, K'.inv_mem hk', ?_⟩
    have h1 : k * k' = k' * k := h k hk k' hk'
    calc (k * k')⁻¹ = (k' * k)⁻¹ := by rw [h1]
      _ = k⁻¹ * k'⁻¹ := by group

private theorem q8_central_sq : ∀ g : QuaternionGroup 2, (∀ h, g * h = h * g) → g * g = 1 := by
  decide

theorem center_sq_of_q8 {K : Subgroup G} (hK : Nonempty (↥K ≃* QuaternionGroup 2)) {k : G}
    (hk : k ∈ K) (hc : ∀ j ∈ K, k * j = j * k) : k * k = 1 := by
  obtain ⟨e⟩ := hK
  have h1 : ∀ h : QuaternionGroup 2, e ⟨k, hk⟩ * h = h * e ⟨k, hk⟩ := by
    intro h
    apply e.symm.injective
    rw [map_mul, map_mul, e.symm_apply_apply]
    exact Subtype.ext (hc _ (e.symm h).2)
  have h2 := q8_central_sq _ h1
  have h3 : e (⟨k, hk⟩ * ⟨k, hk⟩) = e 1 := by rw [map_mul, h2, map_one]
  have h4 := e.injective h3
  exact congrArg Subtype.val h4

theorem center_sup_twins {K K' : Subgroup G} {t : G}
    (hKq : Nonempty (↥K ≃* QuaternionGroup 2)) (hK'q : Nonempty (↥K' ≃* QuaternionGroup 2))
    (hKu : ∀ y ∈ K, y * y = 1 → y = 1 ∨ y = t) (hK'u : ∀ y ∈ K', y * y = 1 → y = 1 ∨ y = t)
    (ht2 : t * t = 1) (hcomm : ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k) :
    ∀ x ∈ K ⊔ K', (∀ y ∈ K ⊔ K', x * y = y * x) → x = 1 ∨ x = t := by
  intro x hx hxc
  obtain ⟨k, hk, k', hk', rfl⟩ := mem_sup_of_commutes hcomm hx
  have hkc : ∀ j ∈ K, k * j = j * k := by
    intro j hj
    have h1 := hxc j (Subgroup.mem_sup_left hj)
    have h2 : k * k' * j = k * j * k' := by
      calc k * k' * j = k * (k' * j) := by group
        _ = k * (j * k') := by rw [← hcomm j hj k' hk']
        _ = k * j * k' := by group
    have h3 : j * (k * k') = j * k * k' := by group
    rw [h2, h3] at h1
    exact mul_right_cancel h1
  have hkc' : ∀ j ∈ K', k' * j = j * k' := by
    intro j hj
    have h1 := hxc j (Subgroup.mem_sup_right hj)
    have h2 : k * k' * j = k * (k' * j) := by group
    have h3 : j * (k * k') = k * (j * k') := by
      calc j * (k * k') = (j * k) * k' := by group
        _ = (k * j) * k' := by rw [hcomm k hk j hj]
        _ = k * (j * k') := by group
    rw [h2, h3] at h1
    exact mul_left_cancel h1
  have hk2 := center_sq_of_q8 hKq hk hkc
  have hk'2 := center_sq_of_q8 hK'q hk' hkc'
  rcases hKu k hk hk2 with rfl | rfl <;> rcases hK'u k' hk' hk'2 with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; exact ht2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
