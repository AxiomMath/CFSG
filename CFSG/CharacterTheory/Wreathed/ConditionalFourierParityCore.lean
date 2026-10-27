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
public import Mathlib.Data.Int.Star
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators

namespace CFSG.Wreathed.ConditionalFourier

variable {ι : Type*} [DecidableEq ι]

@[expose] def unitVector (α : ι) : ι → ℤ := fun χ => if χ = α then 1 else 0

@[simp] theorem unitVector_self (α : ι) : unitVector α α = 1 := by
  simp [unitVector]

theorem unitVector_of_ne {α χ : ι} (h : χ ≠ α) : unitVector α χ = 0 := by
  simp [unitVector, h]

theorem sum_mul_unitVector {B : Finset ι} {α : ι} (hα : α ∈ B) (f : ι → ℤ) :
    ∑ χ ∈ B, f χ * unitVector α χ = f α := by
  simp only [unitVector, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' B α, ite_eq_left hα]

theorem root_of_sq_sum_two {B : Finset ι} {r deg : ι → ℤ} (hdeg : ∀ χ ∈ B, 0 < deg χ)
    (hsq : ∑ χ ∈ B, r χ ^ 2 = 2) (hsum : ∑ χ ∈ B, deg χ * r χ = 0) :
    ∃ α ∈ B, ∃ β ∈ B, α ≠ β ∧ deg α = deg β ∧
      ∀ χ ∈ B, r χ = unitVector α χ - unitVector β χ := by
  classical
  have hle : ∀ χ ∈ B, r χ ^ 2 ≤ 2 := by
    intro χ hχ
    rw [← hsq]
    exact Finset.single_le_sum (f := fun χ => r χ ^ 2) (fun χ _ => sq_nonneg _) hχ
  have hunit : ∀ χ ∈ B, r χ = 0 ∨ r χ = 1 ∨ r χ = -1 := by
    intro χ hχ
    have h := hle χ hχ
    have h1 : -1 ≤ r χ := by nlinarith
    have h2 : r χ ≤ 1 := by nlinarith
    omega
  set T := B.filter (fun χ => r χ ≠ 0) with hT
  have hsqT : ∑ χ ∈ B, r χ ^ 2 = T.card := by
    rw [hT, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    rcases hunit χ hχ with h | h | h <;> simp [h]
  rw [hsq] at hsqT
  have hcard : T.card = 2 := by exact_mod_cast hsqT.symm
  obtain ⟨x, y, hxy, hTxy⟩ := Finset.card_eq_two.mp hcard
  have hxT : x ∈ T := by rw [hTxy]; simp
  have hyT : y ∈ T := by rw [hTxy]; simp
  rw [hT, Finset.mem_filter] at hxT hyT
  have hzero : ∀ χ ∈ B, χ ≠ x → χ ≠ y → r χ = 0 := by
    intro χ hχ hx hy
    by_contra h
    have : χ ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨hχ, h⟩
    rw [hTxy] at this
    simp [hx, hy] at this
  have hsum2 : deg x * r x + deg y * r y = 0 := by
    have hsub : ∑ χ ∈ ({x, y} : Finset ι), deg χ * r χ = ∑ χ ∈ B, deg χ * r χ := by
      apply Finset.sum_subset
      · intro χ hχ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
        rcases hχ with rfl | rfl
        · exact hxT.1
        · exact hyT.1
      · intro χ hχ hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        rw [hzero χ hχ hnot.1 hnot.2, mul_zero]
    rw [Finset.sum_pair hxy, hsum] at hsub
    exact hsub
  have hdx := hdeg x hxT.1
  have hdy := hdeg y hyT.1
  rcases hunit x hxT.1 with hx0 | hx1 | hx1
  · exact absurd hx0 hxT.2
  · rcases hunit y hyT.1 with hy0 | hy1 | hy1
    · exact absurd hy0 hyT.2
    · rw [hx1, hy1] at hsum2
      omega
    · refine ⟨x, hxT.1, y, hyT.1, hxy, by rw [hx1, hy1] at hsum2; omega, fun χ hχ => ?_⟩
      by_cases hχx : χ = x
      · subst hχx
        simp [unitVector, hx1, hxy]
      · by_cases hχy : χ = y
        · subst hχy
          simp [unitVector, hy1, hχx]
        · simp [unitVector, hχx, hχy, hzero χ hχ hχx hχy]
  · rcases hunit y hyT.1 with hy0 | hy1 | hy1
    · exact absurd hy0 hyT.2
    · refine ⟨y, hyT.1, x, hxT.1, hxy.symm, by rw [hx1, hy1] at hsum2; omega, fun χ hχ => ?_⟩
      by_cases hχx : χ = x
      · subst hχx
        simp [unitVector, hx1, hxy]
      · by_cases hχy : χ = y
        · subst hχy
          simp [unitVector, hy1, hχx]
        · simp [unitVector, hχx, hχy, hzero χ hχ hχx hχy]
    · rw [hx1, hy1] at hsum2
      omega

theorem inner_root_root {B : Finset ι} {a b : ι} (ha : a ∈ B) (hb : b ∈ B) (c d : ι) :
    ∑ χ ∈ B, (unitVector a χ - unitVector b χ) * (unitVector c χ - unitVector d χ) =
      (if a = c then 1 else 0) - (if a = d then 1 else 0) - (if b = c then 1 else 0) +
        (if b = d then 1 else 0) := by
  have hexp : ∀ χ, (unitVector a χ - unitVector b χ) * (unitVector c χ - unitVector d χ) =
      unitVector a χ * unitVector c χ - unitVector a χ * unitVector d χ -
        unitVector b χ * unitVector c χ + unitVector b χ * unitVector d χ := fun χ => by ring
  have hprod : ∀ x y : ι, x ∈ B → ∑ χ ∈ B, unitVector x χ * unitVector y χ =
      if x = y then 1 else 0 := by
    intro x y hx
    simp only [unitVector, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' B x]
    simp only [ite_eq_left hx]
  rw [Finset.sum_congr rfl fun χ _ => hexp χ, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, hprod a c ha, hprod a d ha, hprod b c hb, hprod b d hb]

theorem share_of_inner_root_eq_one {a b c d : ι} (hab : a ≠ b) (hcd : c ≠ d)
    (h : ((if a = c then 1 else 0) - (if a = d then 1 else 0) - (if b = c then 1 else 0) +
      (if b = d then 1 else 0) : ℤ) = 1) :
    (a = c ∧ b ≠ d) ∨ (a ≠ c ∧ b = d) := by
  by_cases hac : a = c <;> by_cases hbd : b = d
  · subst hac hbd
    rw [ite_eq_left rfl, ite_eq_right hab, ite_eq_right (Ne.symm hab), ite_eq_left rfl] at h
    omega
  · exact Or.inl ⟨hac, hbd⟩
  · exact Or.inr ⟨hac, hbd⟩
  · rw [ite_eq_right hac, ite_eq_right hbd] at h
    split_ifs at h <;> omega

@[expose] def HasCoefficientShape (B : Finset ι) (c : ι → ℤ) (ones twos : ℕ) : Prop :=
  (∀ χ ∈ B, c χ = 0 ∨ |c χ| = 1 ∨ |c χ| = 2) ∧
    (B.filter fun χ => |c χ| = 1).card = ones ∧ (B.filter fun χ => |c χ| = 2).card = twos

omit [DecidableEq ι] in
theorem hasCoefficientShape_of_sq_sum {B : Finset ι} {c : ι → ℤ} {s : ℕ} (hs : s ≤ 7)
    (h : ∑ χ ∈ B, c χ ^ 2 = s) :
    HasCoefficientShape B c s 0 ∨ (4 ≤ s ∧ HasCoefficientShape B c (s - 4) 1) := by
  have hle : ∀ χ ∈ B, c χ ^ 2 ≤ 7 := by
    intro χ hχ
    have h1 := Finset.single_le_sum (f := fun χ => c χ ^ 2) (fun χ _ => sq_nonneg _) hχ
    rw [h] at h1
    exact h1.trans (by exact_mod_cast hs)
  have hval : ∀ χ ∈ B, c χ = 0 ∨ |c χ| = 1 ∨ |c χ| = 2 := by
    intro χ hχ
    have h1 := hle χ hχ
    have h2 : -2 ≤ c χ := by nlinarith
    have h3 : c χ ≤ 2 := by nlinarith
    rcases abs_cases (c χ) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;> omega
  have hpt : ∀ χ ∈ B, c χ ^ 2 =
      (if |c χ| = 1 then 1 else 0) + 4 * (if |c χ| = 2 then 1 else 0) := by
    intro χ hχ
    rcases hval χ hχ with h0 | h1 | h2
    · simp [h0]
    · rw [← sq_abs, h1]
      norm_num
    · rw [← sq_abs, h2]
      norm_num
  have hcount : (B.filter fun χ => |c χ| = 1).card +
      4 * (B.filter fun χ => |c χ| = 2).card = s := by
    have h' : ((B.filter fun χ => |c χ| = 1).card : ℤ) +
        4 * (B.filter fun χ => |c χ| = 2).card = s := by
      rw [← h, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_boole, Finset.sum_boole]
    exact_mod_cast h'
  by_cases htwo : (B.filter fun χ => |c χ| = 2).card = 0
  · exact Or.inl ⟨hval, by omega, htwo⟩
  · exact Or.inr ⟨by omega, hval, by omega, by omega⟩

end CFSG.Wreathed.ConditionalFourier
