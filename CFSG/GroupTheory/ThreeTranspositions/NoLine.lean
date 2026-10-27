module


import CFSG.Timmesfeld.Closure.Line3
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

namespace CFSG.GroupTheory.ThreeTranspositions

variable {G : Type*} [Group G] [Finite G]

theorem commute_or_orderOf_mul_eq_three {d x : G} (hd : d * d = 1) (hx : x * x = 1)
    (hle : orderOf (d * x) ≤ 3) : Commute d x ∨ orderOf (d * x) = 3 := by
  by_cases h3 : orderOf (d * x) = 3
  · exact Or.inr h3
  · left
    have hlt : orderOf (d * x) < 3 := lt_of_le_of_ne hle h3
    have hpos : 0 < orderOf (d * x) := orderOf_pos (d * x)
    have hcases : orderOf (d * x) = 1 ∨ orderOf (d * x) = 2 := by omega
    have hsq : (d * x) * (d * x) = 1 := by
      rcases hcases with h1 | h2
      · rw [orderOf_eq_one_iff.mp h1]
        simp
      · simpa [pow_two, h2] using pow_orderOf_eq_one (d * x)
    exact (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hd hx).mpr (by
      simpa [pow_two] using hsq)

private theorem false_of_commute_exactly_one {d x y z : G} (hx : Commute d x)
    (hxyz : z = x * y) (hxy : Commute x y) (hx2 : orderOf x = 2)
    (hdy : orderOf (d * y) = 3) (hdz : orderOf (d * z) ≤ 3) : False := by
  have hcomm : Commute x (d * y) := hx.symm.mul_right hxy
  have hcop : (orderOf x).Coprime (orderOf (d * y)) := by
    rw [hx2, hdy]
    norm_num
  have h6 : orderOf (d * z) = 6 := by
    rw [hxyz, hx.left_comm y, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx2, hdy]
  rw [h6] at hdz
  omega

theorem commute_of_mul_mem {D : Set G}
    (hinv : ∀ d ∈ D, orderOf d = 2) (h3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 3)
    {a b : G} (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) {d : G} (hd : d ∈ D) :
    Commute d a := by
  have ha2 : a * a = 1 := by
    simpa [pow_two, hinv a ha] using pow_orderOf_eq_one a
  have hb2 : b * b = 1 := by
    simpa [pow_two, hinv b hb] using pow_orderOf_eq_one b
  have hd2 : d * d = 1 := by
    simpa [pow_two, hinv d hd] using pow_orderOf_eq_one d
  have hab2 : (a * b) * (a * b) = 1 := by
    simpa [pow_two, hinv (a * b) hab] using pow_orderOf_eq_one (a * b)
  have hcomm_ab : Commute a b :=
    (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one ha2 hb2).mpr (by
      simpa [pow_two] using hab2)
  have hba : b * (a * b) = a := by
    rw [← mul_assoc, ← hcomm_ab.eq, mul_assoc, hb2, mul_one]
  by_contra hda
  have hda3 : orderOf (d * a) = 3 := by
    rcases commute_or_orderOf_mul_eq_three hd2 ha2 (h3 d hd a ha) with h | h
    · exact absurd h hda
    · exact h
  by_cases hdb : Commute d b
  · by_cases hdab : Commute d (a * b)
    · refine hda ?_
      have h : Commute d (b * (a * b)) := hdb.mul_right hdab
      rwa [hba] at h
    · exact false_of_commute_exactly_one hdb hcomm_ab.eq hcomm_ab.symm
        (hinv b hb) hda3 (h3 d hd (a * b) hab)
  · have hdb3 : orderOf (d * b) = 3 := by
      rcases commute_or_orderOf_mul_eq_three hd2 hb2 (h3 d hd b hb) with h | h
      · exact absurd h hdb
      · exact h
    by_cases hdab : Commute d (a * b)
    · have hxyz : b = (a * b) * a := by
        calc b = a * (a * b) := by rw [← mul_assoc, ha2, one_mul]
          _ = a * (b * a) := by rw [hcomm_ab.eq]
          _ = (a * b) * a := by group
      exact false_of_commute_exactly_one hdab hxyz
        ((Commute.refl a).mul_right hcomm_ab).symm (hinv (a * b) hab) hda3
        (h3 d hd b hb)
    · have hdab3 : orderOf (d * (a * b)) = 3 := by
        rcases commute_or_orderOf_mul_eq_three hd2 hab2
          (h3 d hd (a * b) hab) with h | h
        · exact absurd h hdab
        · exact h
      exact CFSG.Timmesfeld.Closure.not_orderOf_three_line ha2 hb2 hd2 hcomm_ab
        (by rw [CFSG.Timmesfeld.orderOf_mul_comm_eq]; exact hda3)
        (by rw [CFSG.Timmesfeld.orderOf_mul_comm_eq]; exact hdb3)
        (by rw [CFSG.Timmesfeld.orderOf_mul_comm_eq]; exact hdab3)

theorem mul_not_mem {D : Set G}
    (hinv : ∀ d ∈ D, orderOf d = 2) (h3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 3)
    (hclass : ∀ d ∈ D, ∀ e ∈ D, ∃ x ∈ Subgroup.closure D, e = x * d * x⁻¹)
    {a b : G} (ha : a ∈ D) (hb : b ∈ D) : a * b ∉ D := by
  intro hab
  have hcomm : ∀ d ∈ D, Commute d a := fun d hd =>
    commute_of_mul_mem hinv h3 ha hb hab hd
  have hcomm_closure : ∀ x ∈ Subgroup.closure D, Commute x a := by
    intro x hx
    exact CFSG.Timmesfeld.commute_of_mem_closure
      (S := D) (S' := ({a} : Set G))
      (fun d hd s' hs' => by
        rw [Set.mem_singleton_iff] at hs'
        subst hs'
        exact hcomm d hd) hx (Subgroup.subset_closure (Set.mem_singleton a))
  obtain ⟨x, hx, hb_eq⟩ := hclass a ha b hb
  have hxa : Commute x a := hcomm_closure x hx
  have hba : b = a := by
    rw [hb_eq, hxa.eq, mul_assoc, mul_inv_cancel, mul_one]
  have ha2 : a * a = 1 := by
    simpa [pow_two, hinv a ha] using pow_orderOf_eq_one a
  have h1 : orderOf (a * b) = 2 := hinv (a * b) hab
  rw [hba, ha2, orderOf_one] at h1
  omega

end CFSG.GroupTheory.ThreeTranspositions
