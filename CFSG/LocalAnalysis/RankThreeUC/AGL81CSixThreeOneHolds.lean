module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneSympDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneCaseQ
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneCaseNS
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneCaseNSQuot
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneFive

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

theorem isExtNotation_of_pCore_two_not_le_center {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hGS : G ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hG : oPPrimeHull p G = G) (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn G)
    (hO2 : ¬ CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G) :
    p = 5 ∧ (IsExtNotation (fun A _ => Nonempty (A ≃* alternatingGroup (Fin 5)))
        (fun B _ => IsQ8D8Type B) ↥G ∨
      IsExtNotation (fun A _ => Nat.card A = 5) (fun B _ => IsQ8D8Type B) ↥G) := by
  obtain ⟨hp, hQ, hcard, hC⟩ := structure_of_pCore_two_not_le_center hp5 hGS hG hirr hO2
  exact ⟨hp, isExtNotation_of_pCore_two_isQ8D8Type hp hGS hG hQ hcard hC⟩

section


theorem sympIrredNotQuasisimpleAt_holds {p : ℕ} [Fact p.Prime] : SympIrredNotQuasisimpleAt p := by
  intro hp5 G hGS hG hirr hq
  by_cases hO2 : CFSG.pCore 2 ↥G ≤ Subgroup.center ↥G
  · exact absurd (isQuasisimple_of_pCore_two_le_center hp5 hGS hG hirr hO2) hq
  · exact isExtNotation_of_pCore_two_not_le_center hp5 hGS hG hirr hO2

end

section


theorem sixThreeOne_holds : SixThreeOne :=
  sixThreeOne_of_sympIrredNotQuasisimple fun _ _ => sympIrredNotQuasisimpleAt_holds

end

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
