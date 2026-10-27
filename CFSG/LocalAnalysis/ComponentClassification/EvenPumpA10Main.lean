module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Spor
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Defs

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem a10PumpLeaf_of_clauses
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) : A10PumpLeaf := by
  intro S _ _ hs hna hcat σ P h ⟨eP⟩
  have : IsSimpleGroup S := hs
  have hA : IsA10Type (P ⧸ Open.fusionZStar P) := ⟨eP⟩
  have hodd : OddLieType S → False := fun ho =>
    not_isA10Type_of_properFixedComponent_oddLie hGLS hO hna ho h hA
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, ⟨θ⟩⟩ | ho | he | hsp
  · exact .inl ⟨n, ten_le_of_properFixedComponent_alternating hn θ h hA, ⟨θ⟩⟩
  · exact (hodd ho).elim
  · rcases not_isA10Type_of_properFixedComponent_evenLie hEO hO hna he h with hnA | hU
    · exact (hnA hA).elim
    rcases hU with ho | ⟨n, -, h7, ⟨θ⟩⟩ | hL | hH
    · exact (hodd ho).elim
    · exact .inl ⟨n, ten_le_of_properFixedComponent_alternating (by omega) θ h hA, ⟨θ⟩⟩
    · exact (not_isA10Type_of_properFixedComponent_l34 hL h hA).elim
    · obtain ⟨eH⟩ := hH
      exact (not_isA10Type_of_properFixedComponent_held eH h hA).elim
  · exact .inr (a10SporadicClause_holds hna hsp h hA)

end CFSG.ComponentClassification.EvenPump
