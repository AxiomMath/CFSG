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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Semidihedral.UnitaryDValue.GW

variable {X : Type*} [Group X]

theorem mem_closure_pair {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    {g : X} (hg : g ∈ Subgroup.closure {a, b}) : g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  induction hg using Subgroup.closure_induction with
  | mem c hc =>
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul c d _ _ hc hd =>
    rcases hc with rfl | rfl | rfl | rfl
    · simpa using hd
    · rcases hd with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
    · rcases hd with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inr (Or.inr (Or.inr hab.symm))
      · exact Or.inl hb
      · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]))
    · rcases hd with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inr (Or.inr (Or.inl (by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul])))
      · exact Or.inr (Or.inl (by rw [mul_assoc, hb, mul_one]))
      · exact Or.inl (by rw [mul_assoc, ← mul_assoc b, ← hab, mul_assoc, hb, mul_one, ha])
  | inv c _ hc =>
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rcases hc with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl ha')
    · exact Or.inr (Or.inr (Or.inl hb'))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [mul_inv_rev, ha', hb', hab]

theorem commute_of_sq_commute {g c : X} {r : ℕ} (hr : Odd r) (h2 : g ^ 2 * c = c * g ^ 2)
    (hgr : g ^ r * c = c * g ^ r) : g * c = c * g := by
  obtain ⟨j, rfl⟩ := hr
  have hg : g = ((g ^ 2) ^ j)⁻¹ * g ^ (2 * j + 1) := by
    rw [pow_succ g (2 * j), pow_mul, inv_mul_cancel_left]
  have hc1 : Commute ((g ^ 2) ^ j)⁻¹ c := ((Commute.pow_left h2 j)).inv_left
  have hc2 : Commute (g ^ (2 * j + 1)) c := hgr
  rw [hg]
  exact (hc1.mul_left hc2).eq

theorem exists_cycle_of_odd {a b g : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hne : a ≠ b) {r : ℕ} (hr : Odd r)
    (hgra : g ^ r * a = a * g ^ r) (hgrb : g ^ r * b = b * g ^ r)
    (hga : g * a * g⁻¹ = a ∨ g * a * g⁻¹ = b ∨ g * a * g⁻¹ = a * b)
    (hgb : g * b * g⁻¹ = a ∨ g * b * g⁻¹ = b ∨ g * b * g⁻¹ = a * b) :
    (g * a = a * g ∧ g * b = b * g) ∨
      (g * a * g⁻¹ = b ∧ g * b * g⁻¹ = a * b) ∨
      (g ^ 2 * a * (g ^ 2)⁻¹ = b ∧ g ^ 2 * b * (g ^ 2)⁻¹ = a * b) := by
  have hcomm : ∀ c : X, g * c * g⁻¹ = c → g * c = c * g := fun c h => by
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [h]
  have hsq : ∀ c : X, g ^ r * c = c * g ^ r → g * (g * c * g⁻¹) * g⁻¹ = c → g * c = c * g :=
    fun c hcr h => by
      apply commute_of_sq_commute hr _ hcr
      calc g ^ 2 * c = g * (g * c * g⁻¹) * g⁻¹ * g ^ 2 := by rw [pow_two]; group
        _ = c * g ^ 2 := by rw [h]
  have hmul : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : (a * b) * a = b := by rw [mul_assoc, ← hab, ← mul_assoc, ha, one_mul]
  have e4 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
  have hinj : g * a * g⁻¹ ≠ g * b * g⁻¹ := fun h => hne (by simpa using h)
  rcases hga with h1 | h1 | h1 <;> rcases hgb with h2 | h2 | h2
  · exact absurd (h1.trans h2.symm) hinj
  · exact Or.inl ⟨hcomm a h1, hcomm b h2⟩
  ·
    have hab' : g * (a * b) * g⁻¹ = b := by rw [hmul, h1, h2, e1]
    refine Or.inl ⟨hcomm a h1, hsq b hgrb ?_⟩
    rw [h2, hab']
  ·
    refine Or.inl ⟨hsq a hgra ?_, hsq b hgrb ?_⟩
    · rw [h1, h2]
    · rw [h2, h1]
  · exact absurd (h1.trans h2.symm) hinj
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  ·
    have hab' : g * (a * b) * g⁻¹ = b := by rw [hmul, h1, h2, e2]
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [show g ^ 2 * a * (g ^ 2)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ by rw [pow_two]; group, h1,
        hab']
    · rw [show g ^ 2 * b * (g ^ 2)⁻¹ = g * (g * b * g⁻¹) * g⁻¹ by rw [pow_two]; group, h2, h1]
  ·
    have hab' : g * (a * b) * g⁻¹ = a := by rw [hmul, h1, h2, e4]
    refine Or.inl ⟨hsq a hgra ?_, hcomm b h2⟩
    rw [h1, hab']
  · exact absurd (h1.trans h2.symm) hinj

end CFSG.Semidihedral.UnitaryDValue.GW
