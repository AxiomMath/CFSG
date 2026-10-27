module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAb
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbModels
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbMainLegs
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbMainExc
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Untw

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (center_dvd_table)

theorem tfabClassification_of
    (hGA : CFSG.Open.GriessAllModelsStatement) (hTw : E6RankLowerTw) : TFAbClassification := by
  intro L _ _ hLC hq _ hZ hm hw
  obtain ⟨idx, ⟨e⟩⟩ := hLC
  obtain ⟨t, n, p, f, hmod, hne⟩ := exists_lieModel_valid idx
  have hperf : Group.IsPerfect L := ⟨hq.1⟩
  have hmB : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n p f :=
    blueprintLieModel_of_models (models_lieModel_of_mulEquiv e.symm hmod)
  have htab := center_dvd_table hGA (K := L) (isQuasisimple_of_open' hq) e hmod
  have hZd : 3 ∣ Nat.card (Subgroup.center L) := by rw [hZ]
  have h3t := hZd.trans htab
  rcases case_of_dvd_table Nat.prime_three (by norm_num) h3t with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ |
    ⟨⟨rfl, -, hd⟩ | ⟨rfl, -, hd⟩⟩ | ⟨-, hx⟩
  ·
    exfalso
    have hn2 : 2 ≤ n := hmod.1.2.2.1
    have hpn : 3 ∣ n := hg.trans (Nat.gcd_dvd_left _ _)
    by_cases hn : 4 ≤ n
    · exact lin_four_leg hGA hperf hZ hm e hmod (Or.inl rfl) hn hpn hg
    · obtain rfl : n = 3 := by omega
      exact psl_three_leg hGA hperf hZ hw e hmod (hg.trans (Nat.gcd_dvd_right _ _))
  ·
    have hn3 : 3 ≤ n := hmod.1.2.2.1
    have hpn : 3 ∣ n := hg.trans (Nat.gcd_dvd_left _ _)
    by_cases hn : 4 ≤ n
    · exact (lin_four_leg hGA hperf hZ hm e hmod (Or.inr rfl) hn hpn hg).elim
    · obtain rfl : n = 3 := by omega
      exact psu_three_leg hGA hperf hZ hw e hmod (hg.trans (Nat.gcd_dvd_right _ _))
  ·
    exfalso
    have := (e6RankLowerUntw L n p f hmB hd).1 hZd
    omega
  ·
    exfalso
    have := (hTw L n p f hmB hd).1 hZd
    omega
  ·
    exfalso
    rcases hx with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩
    · exact hne ⟨rfl, rfl, rfl, rfl⟩
    · have := six_le_pRank_of_lieModel_O7 hq (MulEquiv.refl _) hmB hZ
      omega
    · have := four_le_pRank_of_lieModel_G2 (MulEquiv.refl _) hmB hZd
      omega
    · have := five_le_pRank_of_lieModel_U43 (MulEquiv.refl _) hmB hZd
      omega

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
