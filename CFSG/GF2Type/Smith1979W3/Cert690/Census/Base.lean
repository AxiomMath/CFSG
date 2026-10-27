module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.LReduce

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

theorem censusPlus_sound_of (hb : censusBase false () = true)
    (hL : ∀ ci < (candidatesOf false (ldata false ()).Llist).size, CensusLGoal false ci) :
    CensusPlusProp := by
  refine censusPlus_of_reduction (Code.vec (b0Of false)) ?_ ?_
  · intro b hb0 hq
    exact exists_mem_O_map_to_b0 hb hb0 hq
  · intro H hH hN hI L hc ht
    obtain ⟨ci, hci, c, hcO, hcfix, himg⟩ := censusBase_L_reduce hb H L hH hc ht
    have hH' : conjSub H c ≤ O₀ false := conjSub_le_O hH hcO
    have hN' : NoNormalTwo (conjSub H c) := noNormalTwo_conjSub hN
    have hI' : IrreducibleSub (conjSub H c) := irreducibleSub_conj hI
    have hc' : CensusCond false (conjSub H c) (conjSub L c) (Code.vec (b0Of false)) := by
      have h := censusCond_conj hc hcO
      rw [hcfix] at h
      exact h
    have ht' : ∃ t ∈ conjSub L c, IsTypeA (qModel false) t 2 := by
      obtain ⟨t, htL, htA⟩ := ht
      exact ⟨c * t * c⁻¹,
        Subgroup.mem_map.mpr ⟨t, htL, by simp [MulAut.conj_apply]⟩, isTypeA_conj htA hcO⟩
    have hgoal := hL ci hci (conjSub H c) hH' hN' hI' (conjSub L c) himg hc'
    have hconcl : CensusPlusConcl (conjSub H c) := by simpa using hgoal
    rcases hconcl with hΩ | hO | ⟨k, hk, hkH⟩
    · exact Or.inl ((conjSub_eq_omega_iff hcO).mp hΩ)
    · exact Or.inr (Or.inl ((conjSub_eq_O_iff hcO).mp hO))
    · exact Or.inr (Or.inr (exists_conj_KPGL_iff hcO ⟨k, hk, hkH⟩))

theorem censusMinus_sound_of (hb : censusBase true () = true)
    (hL : ∀ ci < (candidatesOf true (ldata true ()).Llist).size, CensusLGoal true ci) :
    CensusMinusProp := by
  refine censusMinus_of_reduction (Code.vec (b0Of true)) ?_ ?_
  · intro b hb0 hq
    exact exists_mem_O_map_to_b0 hb hb0 hq
  · intro H hH hN hI L hc ht
    obtain ⟨ci, hci, c, hcO, hcfix, himg⟩ := censusBase_L_reduce hb H L hH hc ht
    have hH' : conjSub H c ≤ O₀ true := conjSub_le_O hH hcO
    have hN' : NoNormalTwo (conjSub H c) := noNormalTwo_conjSub hN
    have hI' : IrreducibleSub (conjSub H c) := irreducibleSub_conj hI
    have hc' : CensusCond true (conjSub H c) (conjSub L c) (Code.vec (b0Of true)) := by
      have h := censusCond_conj hc hcO
      rw [hcfix] at h
      exact h
    have ht' : ∃ t ∈ conjSub L c, IsTypeA (qModel true) t 2 := by
      obtain ⟨t, htL, htA⟩ := ht
      exact ⟨c * t * c⁻¹,
        Subgroup.mem_map.mpr ⟨t, htL, by simp [MulAut.conj_apply]⟩, isTypeA_conj htA hcO⟩
    have hgoal := hL ci hci (conjSub H c) hH' hN' hI' (conjSub L c) himg hc'
    have hconcl : CensusMinusConcl (conjSub H c) := by simpa using hgoal
    rcases hconcl with hΩ | hO
    · exact Or.inl ((conjSub_eq_omega_iff hcO).mp hΩ)
    · exact Or.inr ((conjSub_eq_O_iff hcO).mp hO)

end CFSG.GF2Type.Smith1979W3.Cert690

end
