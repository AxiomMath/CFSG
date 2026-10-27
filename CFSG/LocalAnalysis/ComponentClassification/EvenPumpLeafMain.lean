module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpLeaf
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporHN

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf

theorem evenAltPumpLeaf_of_clauses
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hspor : EvenAltPumpSporadicClause) :
    EvenAltPumpLeaf := by
  intro S _ _ hs hna hcat σ P h hPex m hm hm10 ⟨eP⟩
  have : IsSimpleGroup S := hs
  have hodd : OddLieType S → False := fun ho =>
    false_of_oddLie_alt_even hGLS hO hna ho h hm hm10 eP
  have hheld : Nonempty (S ≃* NativeSporadic.He) → False := fun ⟨eH⟩ =>
    false_of_held_even hna eH h hm10 eP
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, ⟨θ⟩⟩ | ho | he | ⟨s, ⟨e⟩⟩
  · exact evenAltPumpOutcome_of_alternating hn θ h hm hm10 eP
  · exact (hodd ho).elim
  · rcases uList_of_evenLie_alt_even hEO hGLS hO hna he h hm hm10 eP with
      ho | ⟨n, -, hn7, ⟨θ⟩⟩ | hH
    · exact (hodd ho).elim
    · exact evenAltPumpOutcome_of_alternating (by omega) θ h hm hm10 eP
    · exact (hheld hH).elim
  · by_cases hHe : s = .He
    · subst hHe
      exact (hheld ⟨e⟩).elim
    by_cases hHN : s = .HN
    · subst hHN
      exact Or.inr ⟨eq_ten_of_HN hna e h hPex hm hm10 eP, ⟨e⟩⟩
    · exact (hspor S hna s hHe hHN ⟨e⟩ σ P h hPex m hm hm10 ⟨eP⟩).elim

end CFSG.ComponentClassification.EvenPump
