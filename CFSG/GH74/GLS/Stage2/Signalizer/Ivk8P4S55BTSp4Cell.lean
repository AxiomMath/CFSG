module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4C2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCell
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOF

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.Assembly.LowTwoRank

theorem not_kindFactorAll_classical_of_FSp4 {k : Kind} (hk : IsClassicalKind k) {Y : Type}
    [Group Y] [Finite Y] (hF : FSp4 Y) : ¬ KindFactorAll k Y := by
  intro hkfa
  have hnotL2 := not_isL2_of_FSp4 hF
  obtain ⟨p, e, hp, he, hp2, hlie⟩ := hF
  have hdvd4 := pow_four_dvd_card_of_psp4 hp hp2 hlie
  rcases hk with rfl | ⟨ε, rfl⟩
  · exact hnotL2 hkfa
  · rcases hkfa with h | h
    · exact hnotL2 h
    · have h7 : (p ^ e) ^ 4 ∣ Nat.factorial 7 :=
        hdvd4.trans ((h.card_dvd).trans (card_alt_dvd_factorial 7 (by norm_num)))
      have h11 : (p ^ e) ^ 4 ∣ Nat.factorial 11 :=
        h7.trans (Nat.factorial_dvd_factorial (by norm_num))
      obtain ⟨rfl, rfl⟩ := prime_pow_four_dvd_factorial hp hp2 he h11
      norm_num [Nat.factorial] at h7

theorem vFam_fsp4 : VFam FSp4 where
  iso e h := FSp4.of_mulEquiv e h
  bad _ _ _ _ hk hF := not_kindFactorAll_classical_of_FSp4 hk hF
  char Y _ _ hF := by
    obtain ⟨p, f, hp, hf, hp2, hlie⟩ := hF
    have hd : FSp4d p Y := ⟨f, hf, hlie⟩
    refine ⟨p, ⟨hp, hp2, Or.inr (Or.inr (Or.inr (Or.inl hd)))⟩, fun h120 => ?_,
      outerFalseNS_of_fsp4d hp hp2 hd, fun k hk hBT => ?_⟩
    · have hdvd4 := pow_four_dvd_card_of_psp4 hp hp2 hlie
      have h11 : (p ^ f) ^ 4 ∣ Nat.factorial 11 := (hdvd4.trans h120).trans (by decide)
      obtain ⟨rfl, rfl⟩ := prime_pow_four_dvd_factorial hp hp2 hf h11
      have := hdvd4.trans h120
      norm_num at this
    · obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := Final.lieModel_psp_unpack hlie
      exact BS4.not_btConfig_psp4 hk hp hp2 hf hcard (BTConfig.of_mulEquiv e hBT)

theorem cellV_fsp4 (hInv : InvSec) (hX : Cross55) : CellV FSp4 :=
  cellV_of_vfam hInv hX vFam_fsp4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
