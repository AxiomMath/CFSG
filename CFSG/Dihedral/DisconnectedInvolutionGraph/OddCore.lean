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

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

@[expose] def oddCore (G : Type*) [Group G] : Subgroup G :=
  sSup {subgroup : Subgroup G | subgroup.Normal ∧ Odd (Nat.card subgroup)}

theorem oddCore_normal : (oddCore G).Normal :=
  Subgroup.sSup_normal _ (fun _ hmem => hmem.1)

theorem normal_odd_le_oddCore (subgroup : Subgroup G)
    (hnormal : subgroup.Normal) (hodd : Odd (Nat.card subgroup)) : subgroup ≤ oddCore G :=
  le_sSup ⟨hnormal, hodd⟩

theorem normal_odd_sup_odd [Finite G] (first second : Subgroup G)
    (hfirstNormal : first.Normal) (hsecondNormal : second.Normal)
    (hfirstOdd : Odd (Nat.card first)) (hsecondOdd : Odd (Nat.card second)) :
    Odd (Nat.card (first ⊔ second : Subgroup G)) := by
  let _ := hfirstNormal
  let _ := hsecondNormal
  have hindexOdd : Odd (first.relIndex (first ⊔ second)) := by
    rw [Subgroup.relIndex_sup_left]
    exact hsecondOdd.of_dvd_nat (first.relIndex_dvd_card second)
  let within := first.subgroupOf (first ⊔ second)
  have hwithinCard : Nat.card within = Nat.card first :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show first ≤ first ⊔ second from le_sup_left)).toEquiv
  have hproduct := within.index_mul_card
  have hindex : within.index = first.relIndex (first ⊔ second) := rfl
  rw [hindex, hwithinCard] at hproduct
  rw [← hproduct]
  exact hindexOdd.mul hfirstOdd

theorem oddCore_odd [Finite G] : Odd (Nat.card (oddCore G)) := by
  classical
  have hbot : (⊥ : Subgroup G).Normal ∧ Odd (Nat.card (⊥ : Subgroup G)) := by
    exact ⟨inferInstance, by rw [Subgroup.card_bot]; decide⟩
  obtain ⟨maximal, _, hmaximal⟩ := Finite.exists_le_maximal
    (α := Subgroup G) (p := fun subgroup => subgroup.Normal ∧ Odd (Nat.card subgroup)) hbot
  have hallLe : ∀ subgroup : Subgroup G, subgroup.Normal → Odd (Nat.card subgroup) →
      subgroup ≤ maximal := by
    intro subgroup hnormal hodd
    have hsupNormal : (maximal ⊔ subgroup).Normal := by
      let _ := hmaximal.prop.1
      let _ := hnormal
      infer_instance
    have hsupOdd := normal_odd_sup_odd maximal subgroup hmaximal.prop.1 hnormal
      hmaximal.prop.2 hodd
    have heq := hmaximal.eq_of_le ⟨hsupNormal, hsupOdd⟩ le_sup_left
    exact heq ▸ le_sup_right
  have hequal : oddCore G = maximal := by
    apply le_antisymm
    · exact sSup_le (fun subgroup hmem => hallLe subgroup hmem.1 hmem.2)
    · exact normal_odd_le_oddCore maximal hmaximal.prop.1 hmaximal.prop.2
  rw [hequal]
  exact hmaximal.prop.2

theorem oddCore_characteristic [Finite G] : (oddCore G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro automorphism
  have hmapNormal := (oddCore_normal (G := G)).map automorphism.toMonoidHom
    automorphism.surjective
  have hmapOdd : Odd (Nat.card ((oddCore G).map automorphism.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective automorphism.injective]
    exact oddCore_odd
  exact normal_odd_le_oddCore _ hmapNormal hmapOdd

end CFSG.DisconnectedInvolutionGraph.Helpers
