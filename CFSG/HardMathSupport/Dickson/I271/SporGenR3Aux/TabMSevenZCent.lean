module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenEmb

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
  _root_.Timmesfeld.PcReg _root_.Timmesfeld.Mon7

section Cent


theorem seven_pow_dvd_card_cent_zG :
    7 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({zG} : Set Gmat)) := by
  have : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  have hP : CFSG.KC.BM.PcFive.PSub (gq 0) qR ≤ Subgroup.centralizer ({gq 5} : Set Gmat) := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (pcHyp_gq.rel.zc i).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact gq_comm_five (by norm_num)
  rw [← card_centralizer_eq_of_isConj isConj_gq_five, ← card_PSub_gq]
  exact Subgroup.card_dvd_of_le hP

end Cent

section Classes


theorem isConj_zG_of_not_conj {z : Gmat} (hz : orderOf z = 7)
    (hzd : ∀ (g : Gmat) (m : ℕ), g * z * g⁻¹ ≠ dG ^ m) : IsConj z zG := by
  rcases monsterSevenClasses z hz with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact absurd (hc.trans (pow_one dG).symm) (hzd c 1)
  · exact h

theorem seven_pow_dvd_of_not_conj {z : Gmat} (hz : orderOf z = 7)
    (hzd : ∀ (g : Gmat) (m : ℕ), g * z * g⁻¹ ≠ dG ^ m) :
    7 ^ 6 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set Gmat)) := by
  rw [card_centralizer_eq_of_isConj (isConj_zG_of_not_conj hz hzd)]
  exact seven_pow_dvd_card_cent_zG

end Classes

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
