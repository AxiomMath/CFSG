module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.CatLeaf

theorem y923_lieRestAt_psuGood (hO : LieOrderFormulasInput) : Y923_LieRestAt FamPsuGood := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain ⟨rfl, hn3, hdiv⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  have hne : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
  exact noL2_of_famOK hq e0 (famOK_psu hO h hn3 hne hdiv) h3 hnot hJ hr

section Closed


theorem y923_psuGood_holds : Y923_PsuGood :=
  y923_lieRestAt_psuGood CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

end Closed

end CFSG.HardMathSupport.Dickson.Sec6.I923
