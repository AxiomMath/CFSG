module

public import CFSG.Certificates.Kernel.SporSch.ThirdLowerPrelude



public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

variable (h : ECheckH)
include h

theorem locE_le_H3H :
    locE ≤ locH3 := by
  rw [locE, Subgroup.closure_le]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
  rw [gTuple_length] at hi
  rw [gTuple_getD hi]
  refine mem_locH3.2 ⟨?_, ?_⟩
  · rw [← co2Q_originalSubgroup]
    exact (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
      (rep_gPermH h hi)).1 (gFactsH h hi).2.1
  · exact ((eqA_iff (rep_compA (rep_gPermH h hi) rep_u) (rep_compA rep_u (rep_gPermH h hi))).1
      (gFactsH h hi).2.2).symm

theorem le_card_locH3 :
    1474560 ≤ Nat.card locH3 := by
  rw [← card_locEH h]
  exact Subgroup.card_le_of_le (locE_le_H3H h)

end CFSG.Sporadic.Co2Schreier
