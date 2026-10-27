module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5T1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5T2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dL5T3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5AtlasProved

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dL5Proof

open K21dA8Proof

theorem k21dGeomAt_SL5 : K21dGeomAt SL5 := by
  rw [k21dGeomAt_iff]
  intro U D E hUDE
  obtain ⟨hU, hUD, hDs, hED, hE, hE9, hinv⟩ := hUDE
  obtain ⟨c, hc⟩ := exists_conj_upperSub5 hU
  have hU' : U.map (MulAut.conj c⁻¹).toMonoidHom = upperSub5 := by
    rw [hc, map_conj_inv_conj]
  have hyp := K21dHyp.map (MulAut.conj c⁻¹) ⟨hU, hUD, hDs, hED, hE, hE9, hinv⟩
  rw [hU'] at hyp
  obtain ⟨-, hUD', hDs', hED', -, hE9', -⟩ := hyp
  have hconcl : K21dConcl upperSub5 (E.map (MulAut.conj c⁻¹).toMonoidHom) := by
    rcases exists_good_of_solvable hUD' hDs' with h | h | h
    · exact concl_good1 (hED'.trans h) hE9'
    · exact concl_good2 (hED'.trans h) hE9'
    · exact concl_good3 (hED'.trans h) hE9'
  exact K21dConcl.of_map (MulAut.conj c⁻¹) (by rw [hU']; exact hconcl)

end K21dL5Proof

theorem k21dGeomL5_holds : K21dGeomL5 := by
  intro S _ _ hS
  obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.McLaughlin.nonempty_equiv_G52_of_isL5Two hS
  exact K21dA8Proof.k21dGeomAt_of_mulEquiv (e.trans K21dL5Proof.slEquivGL5.symm)
    K21dL5Proof.k21dGeomAt_SL5

end CFSG.LocalAnalysis.RankThreeUC.S15
