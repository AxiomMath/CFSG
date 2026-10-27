module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MOddCore

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

theorem eq_bot_of_normal_odd_of_oddCore {X : Type*} [Group X] {C P : Subgroup X}
    (hC : CFSG.oddCore ↥C = ⊥) (hP : P ≤ C) (hPn : (P.subgroupOf C).Normal)
    (hodd : Odd (Nat.card P)) : P = ⊥ := by
  have hle : P.subgroupOf C ≤ CFSG.oddCore ↥C := by
    refine le_sSup ⟨hPn, ?_⟩
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv]
  rw [hC, le_bot_iff, Subgroup.subgroupOf_eq_bot] at hle
  exact disjoint_self.1 (hle.mono_right hP)

theorem involutionOddCoreTrivial_of_oddCore {Y : Type} [Group Y]
    (h : ∀ t : Y, orderOf t = 2 → CFSG.oddCore ↥(centralizer ({t} : Set Y)) = ⊥) :
    InvolutionOddCoreTrivial Y := fun t ht _ hP hPn hodd =>
  eq_bot_of_normal_odd_of_oddCore (h t ht) hP hPn hodd

theorem autOddCoreTrivial_of_oddCore {Y : Type} [Group Y]
    (h : ∀ ν : MulAut Y, ν ≠ 1 → ν * ν = 1 → CFSG.oddCore ↥(fixSubgroup ν) = ⊥) :
    AutOddCoreTrivial Y := fun ν hν1 hνν _ hP hPn hodd =>
  eq_bot_of_normal_odd_of_oddCore (h ν hν1 hνν) hP hPn hodd

end CFSG.EvenSporadicStandard.Induction
