module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGADefs
public import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall

public section

namespace CFSG.ComponentClassification.TBLit

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt

theorem griessMultipliersOdd_holds :
    GriessMultipliersOdd := by
  intro X _ t n p f hmodel hp2 hrow
  rcases hrow with rfl | ⟨rfl, hn⟩
  · exact GriessClassical.griess_classical_of_large .PSL hmodel (Or.inl rfl)
  obtain ⟨hp, hf, hn3, -⟩ := hmodel.1
  by_cases hq : 4 ≤ p ^ f
  · exact GriessClassical.griess_classical_of_large .PSU hmodel
      (Or.inr (Or.inl ⟨rfl, hn, Or.inl hq⟩))
  have hp3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
  have h3 : p ^ f = 3 := by omega
  obtain ⟨rfl, rfl⟩ := GriessClassical.GriessExceptionalPow.eq_three_one_of_pow_eq_three hp
    (by omega) h3
  by_cases h6 : 6 ≤ n
  · exact GriessClassical.griess_classical_of_large .PSU hmodel
      (Or.inr (Or.inl ⟨rfl, hn, Or.inr (Or.inr ⟨by norm_num, h6⟩)⟩))
  obtain ⟨k, hk⟩ := hn
  obtain rfl : n = 4 := by omega
  exact GriessClassical.psu_four_three_row hmodel

end CFSG.ComponentClassification.TBLit
