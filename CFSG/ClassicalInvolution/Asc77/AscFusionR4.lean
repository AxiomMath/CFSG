module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

variable {Q : Type*} [Group Q]

theorem exists_inverted_order_four (z : Q) (hz2 : z * z = 1)
    (h2 : ∀ x : Q, ∃ k : ℕ, x ^ (2 ^ k) = 1)
    (hzu : ∀ x : Q, x * x = 1 → x = 1 ∨ x = z)
    (hgen : ∀ H : Subgroup Q, (∀ x : Q, orderOf x = 4 → x ∈ H) → H = ⊤)
    (τ : Q ≃* Q) (hτ2 : ∀ x, τ (τ x) = x) (hτ1 : ∃ x, τ x ≠ x) :
    ∃ κ : Q, orderOf κ = 4 ∧ τ κ = κ⁻¹ := by
  have hsq : ∀ x : Q, orderOf x = 4 → x * x = z := by
    intro x hx
    have h1 : (x * x) * (x * x) = 1 := by
      have : x ^ 4 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      calc (x * x) * (x * x) = x ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    rcases hzu (x * x) h1 with h | h
    · exfalso
      have : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hx] at this
      omega
    · exact h
  by_cases hA : ∃ g : Q, ¬ (g * (τ g)⁻¹) * (g * (τ g)⁻¹) = 1
  · obtain ⟨g, hg⟩ := hA
    set κ₀ : Q := g * (τ g)⁻¹ with hκ₀
    have hτκ₀ : τ κ₀ = κ₀⁻¹ := by
      rw [hκ₀, map_mul, map_inv, hτ2]
      group
    obtain ⟨k, hk⟩ := h2 κ₀
    obtain ⟨e, he, hoe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have he2 : 2 ≤ e := by
      by_contra hlt
      have hle : orderOf κ₀ ∣ 2 := by
        rw [hoe]
        exact pow_dvd_pow 2 (by omega : e ≤ 1)
      exact hg (by rw [← pow_two]; exact orderOf_dvd_iff_pow_eq_one.mp hle)
    refine ⟨κ₀ ^ (2 ^ (e - 2)), ?_, ?_⟩
    · rw [orderOf_pow_of_dvd (by positivity) (by rw [hoe]; exact pow_dvd_pow 2 (by omega)), hoe]
      have : 2 ^ e = 2 ^ (e - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      rw [this, Nat.mul_div_cancel_left _ (by positivity)]
    · rw [map_pow, hτκ₀, inv_pow]
  · push Not at hA
    have hfix : ∀ g : Q, τ g = g ∨ τ g = z * g := by
      intro g
      rcases hzu _ (hA g) with h | h
      · left
        have : g = τ g := by
          have := mul_inv_eq_one.mp h
          exact this
        exact this.symm
      · right
        have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
        have h' : g * (τ g)⁻¹ = z := h
        have h'' : g = z * τ g := by
          have := congrArg (fun x => x * τ g) h'
          simpa [mul_assoc] using this
        have : τ g = z⁻¹ * g := by
          rw [h'', hz1, ← mul_assoc, hz2, one_mul]
          simp [← h'']
        rw [this, hz1]
    set H : Subgroup Q := MonoidHom.eqLocus τ.toMonoidHom (MonoidHom.id Q) with hH
    have hHne : H ≠ ⊤ := by
      intro h
      obtain ⟨x, hx⟩ := hτ1
      have : x ∈ H := by rw [h]; trivial
      exact hx this
    have hex : ∃ g : Q, orderOf g = 4 ∧ g ∉ H := by
      by_contra hno
      push Not at hno
      exact hHne (hgen H hno)
    obtain ⟨g, hg4, hgH⟩ := hex
    refine ⟨g, hg4, ?_⟩
    have hgτ : τ g ≠ g := fun h => hgH h
    have hτg : τ g = z * g := (hfix g).resolve_left hgτ
    have hginv : g⁻¹ = z * g := by
      have h4 : g ^ 4 = 1 := by rw [← hg4]; exact pow_orderOf_eq_one g
      have h3 : g⁻¹ = g * g * g :=
        inv_eq_of_mul_eq_one_right (by
          calc g * (g * g * g) = g ^ 4 := by simp [pow_succ, mul_assoc]
            _ = 1 := h4)
      rw [h3, ← hsq g hg4]
    rw [hτg, hginv]

theorem quaternion_generated_by_order_four {n : ℕ} [NeZero n] {Q : Type*} [Group Q]
    (e : Q ≃* QuaternionGroup n) (H : Subgroup Q) (hH : ∀ x : Q, orderOf x = 4 → x ∈ H) :
    H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hxa : ∀ k : ZMod (2 * n), e.symm (QuaternionGroup.xa k) ∈ H := fun k =>
    hH _ (by rw [MulEquiv.orderOf_eq]; exact QuaternionGroup.orderOf_xa k)
  have hx : x = e.symm (e x) := by simp
  rw [hx]
  generalize e x = y
  cases y with
  | a k =>
    have : (QuaternionGroup.a k : QuaternionGroup n) =
        QuaternionGroup.xa 0 * QuaternionGroup.xa (k - (n : ZMod (2 * n))) := by
      rw [QuaternionGroup.xa_mul_xa]
      congr 1
      ring
    rw [this, map_mul]
    exact H.mul_mem (hxa 0) (hxa _)
  | xa k => exact hxa k

end CFSG.ClassicalInvolution.Asc77.AscFusion
