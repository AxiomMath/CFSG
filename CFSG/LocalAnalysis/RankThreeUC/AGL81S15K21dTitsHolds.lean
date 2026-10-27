module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsSL
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsSU
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsSp4
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsG2

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

section Holds


open K21dTitsProof in
theorem k21dGeomTits_holds : K21dGeomTits := by
  intro S _ _ h
  refine k21dGeomAt_of_solvOver fun U hU' => ?_
  have hU := isSylowTwoOf_of_isSylowOf_two hU'
  rcases h with ⟨d, Q, hQ, hd, ⟨e⟩⟩ | ⟨d, Q, hQ4, hd, ⟨e⟩⟩
  · obtain ⟨d1, hv⟩ := d
    simp only at hd
    rcases hd with rfl | rfl | rfl | ⟨rfl, hQ2⟩
    · exact solvOver_of_typeG2 hv hQ e hU
    · exact solvOver_of_typeB2 hv hQ e hU
    · exact solvOver_of_typeA3 hv hQ e hU
    · exact solvOver_of_typeTwistedA3 hv hQ hQ2 e hU
  · obtain ⟨d1, hv⟩ := d
    simp only at hd
    subst hd
    exact solvOver_of_typeTwistedA4 hv hQ4 e hU

end Holds

end CFSG.LocalAnalysis.RankThreeUC.S15
