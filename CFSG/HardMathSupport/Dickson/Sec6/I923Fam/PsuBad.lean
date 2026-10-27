module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.Diag
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.Cyclic
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartTwo.KFacts CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms

theorem y923_lieRestAt_psuBad (hO : LieOrderFormulasInput) (hGA : GriessAllModelsStatement) :
    Y923_LieRestAt FamPsuBad := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  obtain ⟨rfl, hn3, hdvd⟩ := hF
  by_cases h6 : n = 6 ∧ p = 2 ∧ f = 1
  · exact y923_lieRestAt_psuSixTwo hO Y hq hcore hL2 .PSU n p f hadm ht ⟨rfl, h6⟩ hm α h3 hnot J hJ
      r hr
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  have hne : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
  have hψ3 : (MulAut.congr e0 (centerDescend Y α)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  by_cases hσ : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne
      (MulAut.congr e0 (centerDescend Y α)) = 1
  · exfalso
    apply hnot
    have hD : MulAut.congr e0 (centerDescend Y α) ∈
        primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn3 hne]
      exact hσ
    have h1 : ¬(n = 4 ∧ p = 2 ∧ f = 1) := by
      rintro ⟨rfl, rfl, rfl⟩
      revert hdvd
      norm_num
    have h3' : ¬(n = 4 ∧ p = 3 ∧ f = 1) := by
      rintro ⟨rfl, rfl, rfl⟩
      revert hdvd
      norm_num
    have hM := isCyclic_hopfMultiplier_psu hGA ((lieModel_classical_iff (by decide)).mp hm)
      h1 h6 h3'
    exact mem_innAutDerived_of_diag hq h e0 hM h3 hD
  · obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one h hn3 hne hψ3 hσ
    exact noL2_of_conj_descent e0 α rfl hu (noL2Layer_fieldAut_psu hO h hn3 hσord) hJ hr

section Closed


theorem y923_psuBad_holds (hGA : GriessAllModelsStatement) : Y923_PsuBad :=
  y923_lieRestAt_psuBad CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hGA

end Closed

end CFSG.HardMathSupport.Dickson.Sec6.I923
