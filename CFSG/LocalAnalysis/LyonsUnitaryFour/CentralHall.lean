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
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LyonsUnitaryFour

variable {G : Type*} [Group G] [Finite G]

theorem central_hall_direct_complement (A : Subgroup G) (hA : A ≤ Subgroup.center G)
    (hcop : Nat.Coprime (Nat.card A) A.index) :
    ∃ K : Subgroup G, Nat.card K = A.index ∧ A ⊔ K = ⊤ ∧ A ⊓ K = ⊥ ∧
      (∀ g : G, g ∈ K ↔ g ^ A.index = 1) ∧ K.Characteristic ∧
      ∀ L : Subgroup G, Nat.card L = A.index → L = K := by
  classical
  have hAnormal : A.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have h := Subgroup.mem_center_iff.mp (hA ha) g
    rw [h, mul_inv_cancel_right]
    exact ha
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hpowcard : ∀ (L : Subgroup G) (g : G), g ∈ L → g ^ Nat.card L = 1 := by
    intro L g hg
    have h := congrArg Subtype.val (pow_card_eq_one' (G := L) (x := ⟨g, hg⟩))
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  have hcard : Nat.card A * Nat.card K = Nat.card G := hK.card_mul_card
  have hindex : Nat.card K = A.index := by
    have h := A.card_mul_index
    have hApos : 0 < Nat.card A := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hApos (hcard.trans h.symm)
  have hsup : A ⊔ K = ⊤ := hK.sup_eq_top
  have hinf : A ⊓ K = ⊥ := disjoint_iff.mp hK.disjoint
  have hpowA : ∀ a ∈ A, a ^ A.index = 1 → a = 1 := by
    intro a ha han
    have h1 : orderOf a ∣ A.index := orderOf_dvd_of_pow_eq_one han
    have h2 : orderOf a ∣ Nat.card A := by
      rw [← Subgroup.orderOf_mk a ha]
      exact orderOf_dvd_natCard _
    have := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    exact orderOf_eq_one_iff.mp this
  have hdecomp : ∀ g : G, ∃ a ∈ A, ∃ k ∈ K, g = a * k := by
    intro g
    have hg : g ∈ A ⊔ K := hsup ▸ Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hg
    obtain ⟨a, ha, k, hk, rfl⟩ := hg
    exact ⟨a, ha, k, hk, rfl⟩
  have hKmem : ∀ g : G, g ∈ K ↔ g ^ A.index = 1 := by
    intro g
    constructor
    · intro hg
      rw [← hindex]
      exact hpowcard K g hg
    · intro hg
      obtain ⟨a, ha, k, hk, rfl⟩ := hdecomp g
      have hak : Commute a k := (Subgroup.mem_center_iff.mp (hA ha) k).symm
      have hkn : k ^ A.index = 1 := by
        rw [← hindex]
        exact hpowcard K k hk
      rw [hak.mul_pow, hkn, mul_one] at hg
      rw [hpowA a ha hg, one_mul]
      exact hk
  refine ⟨K, hindex, hsup, hinf, hKmem, ?_, ?_⟩
  · refine ⟨fun φ => ?_⟩
    ext g
    rw [Subgroup.mem_comap, hKmem, hKmem]
    constructor
    · intro h
      have := congrArg φ.symm h
      simpa [← map_pow] using this
    · intro h
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, h, map_one]
  · intro L hL
    apply Subgroup.eq_of_le_of_card_ge _ (by rw [hindex, hL])
    intro g hg
    rw [hKmem, ← hL]
    exact hpowcard L g hg

end CFSG.LyonsUnitaryFour
