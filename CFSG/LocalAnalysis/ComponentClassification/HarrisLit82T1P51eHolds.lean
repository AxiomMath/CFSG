module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eBlock
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eOrthFam
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eSpFam

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG CFSG.ComponentClassification.CatLeaf

theorem not_isCoverOf_holds
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsSimpleChevalleyOver p X) {z : X} (hz : orderOf z = 2) {J : Subgroup X}
    (hJ : IsTwoComponentIn J (Subgroup.centralizer {z})) {r : ℕ} (hr : 1 ≤ r) :
    ¬ IsCoverOf .POmegaOdd 3 p r 2 (↥J ⧸ pPrimeCore 2 ↥J) := by
  have hO : LieOrderFormulasInput := CatLeafProof.lieOrderFormulasInput
  exact not_isCoverOf_of_famCases
    (Sp.famNoSpin7_psp (fun h2 ha hL ht => noSpin7_of_lieModel hO h2 ha hL ht)
      (fun hp hp2 hK e => noSpin7_of_mulEquiv_statedSp hp hp2 hK e)).famCases
    (Orth.famNoSpin7_pomegaOdd (fun h2 ha hL ht => noSpin7_of_lieModel hO h2 ha hL ht)
      noSpin7_blockP).famCases
    (Orth.famNoSpin7_pomegaPlus (fun h2 ha hL ht => noSpin7_of_lieModel hO h2 ha hL ht)
      noSpin7_blockP).famCases
    (Orth.famNoSpin7_pomegaMinus (fun h2 ha hL ht => noSpin7_of_lieModel hO h2 ha hL ht)
      noSpin7_blockP).famCases X hp hp2 hX hz hJ hr

theorem harris82Lemma51e_holds :
    Harris82Lemma51e := by
  have hO : LieOrderFormulasInput := CatLeafProof.lieOrderFormulasInput
  exact harris82Lemma51e_of_famCases
    (Sp.famNoSpin7_psp (fun h2 ha hL ht => noSpin7_of_lieModel hO h2 ha hL ht)
      (fun hp hp2 hK e => noSpin7_of_mulEquiv_statedSp hp hp2 hK e)).famCases
    (Orth.famNoSpin7_pomegaOdd (fun h2 ha hL ht => noSpin7_of_lieModel hO h2 ha hL ht)
      noSpin7_blockP).famCases
    (Orth.famNoSpin7_pomegaPlus (fun h2 ha hL ht => noSpin7_of_lieModel hO h2 ha hL ht)
      noSpin7_blockP).famCases
    (Orth.famNoSpin7_pomegaMinus (fun h2 ha hL ht => noSpin7_of_lieModel hO h2 ha hL ht)
      noSpin7_blockP).famCases

end CFSG.ComponentClassification.HarrisLit.T1.P51e
