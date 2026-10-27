module

public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem fl3_card_aut_dvd {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (_hp : p.Prime)
    (_hf : 1 ≤ f) (_hp2 : p ≠ 2) (hLie : LieModel Y .PSL 3 p f) :
    Nat.card (MulAut Y) ∣ Nat.card Y * (6 * f) := by
  have hcl : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL 3 p f :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLie
  obtain ⟨-, -, -, -, hO⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound Y 3 p f hcl
  have h1 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ∣
      2 * f * Nat.gcd 3 (p ^ f - 1) := hO le_rfl
  have h2 : Nat.gcd 3 (p ^ f - 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have h3 : 2 * f * Nat.gcd 3 (p ^ f - 1) ∣ 6 * f := by
    have h4 : 2 * f * Nat.gcd 3 (p ^ f - 1) ∣ 2 * f * 3 := mul_dvd_mul_left (2 * f) h2
    rwa [show 2 * f * 3 = 6 * f by ring] at h4
  have hinn : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner Y) ∣
      Nat.card Y := by
    have := Subgroup.card_ker_mul_card_range (MulAut.conj : Y →* MulAut Y)
    exact Dvd.intro_left _ this
  have hcard : Nat.card (MulAut Y) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) *
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner Y) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hcard, mul_comm]
  exact mul_dvd_mul hinn (h1.trans h3)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
