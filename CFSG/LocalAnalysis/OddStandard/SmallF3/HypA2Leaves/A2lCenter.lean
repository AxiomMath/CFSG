module

public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt.GriessClassical

theorem a2l_center_eq_bot_of_row {Y : Type} [Group Y] [Group.IsPerfect Y]
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hrow : Nonempty (CFSG.Open.griessHopfMultiplier (Y ⧸ center Y) ≃*
      generic t n p f × exceptional t n p f))
    (hg : genericOrders t n p f = (1, 1)) (he : exceptionalOrders t n p f = (1, 1)) :
    center Y = ⊥ := by
  obtain ⟨e⟩ := hrow
  have h1 : Nat.card (Multiplicative (ZMod 1)) = 1 := by
    rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_zmod]
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (Y ⧸ center Y)) = 1 := by
    rw [Nat.card_congr e.toEquiv]
    simp only [generic, exceptional, hg, he, Nat.card_prod, h1, mul_one]
  have hdvd :=
    ComponentClassification.CatFactsL4U4.Cover82.Mult.card_center_dvd_hopfMultiplier (Q := Y)
      (S := Y ⧸ center Y) (MulEquiv.refl (Y ⧸ center Y))
  rw [hcard] at hdvd
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 hdvd)

theorem a2l_center_eq_bot_psp44
    {Y : Type} [Group Y] (hY : CFSG.IsQuasisimple Y)
    (hL : LieModel (Y ⧸ center Y) .PSp 2 2 2) : center Y = ⊥ := by
  haveI : Group.IsPerfect Y := hY.1
  obtain ⟨-, hrow⟩ := psp_row (hL.statedClassicalModel_of_ne_zero (by norm_num))
    (Or.inr (Or.inl rfl))
  exact a2l_center_eq_bot_of_row hrow (by decide) (by decide)

theorem a2l_center_eq_bot_psl52
    {Y : Type} [Group Y]
    (hY : CFSG.IsQuasisimple Y) (hL : LieModel (Y ⧸ center Y) .PSL 5 2 1) : center Y = ⊥ := by
  haveI : Group.IsPerfect Y := hY.1
  obtain ⟨-, hrow⟩ := psl_row (hL.statedClassicalModel_of_ne_zero (by norm_num))
  exact a2l_center_eq_bot_of_row hrow (by decide) (by decide)

theorem a2l_center_eq_bot_psu52
    {Y : Type} [Group Y] (hY : CFSG.IsQuasisimple Y)
    (hL : LieModel (Y ⧸ center Y) .PSU 5 2 1) : center Y = ⊥ := by
  haveI : Group.IsPerfect Y := hY.1
  obtain ⟨-, hrow⟩ := psu_odd_row (hL.statedClassicalModel_of_ne_zero (by norm_num))
    (by decide)
  exact a2l_center_eq_bot_of_row hrow (by decide) (by decide)

end CFSG.OddStandard.SmallF3.HypA2Leaves
