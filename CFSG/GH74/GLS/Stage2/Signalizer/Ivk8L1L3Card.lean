module

public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem fl3_card_formula {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (_hp : p.Prime)
    (_hf : 1 ≤ f) (_hp2 : p ≠ 2) (hLie : LieModel Y .PSL 3 p f) :
    Nat.card Y * Nat.gcd 3 (p ^ f - 1) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) := by
  have hcl : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 3 p f :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLie
  obtain ⟨hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound Y 3 p f hcl
  set q := p ^ f with hq
  have hprod : ∏ j ∈ Finset.Icc 2 3, (q ^ j - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have hdvd : Nat.gcd 3 (q - 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    have h1 : Nat.gcd 3 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 2 - 1 := by
      simpa using (Nat.sub_dvd_pow_sub_pow q 1 2)
    exact (h1.trans h2).trans ((dvd_mul_right _ _).trans (dvd_mul_left _ _))
  rw [hprod] at hord
  have hnum : q ^ (3 * (3 - 1) / 2) = q ^ 3 := by norm_num
  rw [hnum] at hord
  rw [hord, Nat.div_mul_cancel hdvd]
  ring

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
