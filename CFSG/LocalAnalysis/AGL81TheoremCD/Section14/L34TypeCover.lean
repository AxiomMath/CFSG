module

public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Sylow
import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsBase
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

theorem isLThreeFour_or_isSLThreeFour_of_isL34Type
    {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple Y) (hO : CFSG.pPrimeCore 3 Y = ⊥)
    (hL : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsL34Type Y) :
    CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour Y ∨
      CFSG.LocalAnalysis.GLTheoremB.IsSLThreeFour Y := by
  obtain ⟨d, ⟨q, hq4, hd⟩, ⟨e⟩⟩ := hL
  obtain ⟨eproj⟩ := nonempty_mulEquiv_projSL_of_lie_A2_four d ⟨q, hq4, hd⟩
  have hL3 : CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour (Y ⧸ Subgroup.center Y) := by
    refine ⟨GaloisField 2 2, inferInstance, inferInstance, ?_, ?_⟩
    · rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    · exact ⟨e.trans (eproj.trans (CFSG.PGLModel.projSLEquivStatedProj 3
        (GaloisField 2 2)))⟩
  have hq' : CFSG.Open.IsQuasisimple Y :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff Y).2.2.1).mp hq
  have hpc : CFSG.pCore 3 Y = Subgroup.center Y :=
    CFSG.HardMathSupport.Solomon.Coordinator.i271h_pCore_three_eq_center hq' hO
  have hL3' : CFSG.LocalAnalysis.GLTheoremB.IsLThreeFour (Y ⧸ CFSG.pCore 3 Y) := by
    obtain ⟨K, hKf, hKfin, hK4, ⟨e3⟩⟩ := hL3
    exact ⟨K, hKf, hKfin, hK4,
      ⟨(QuotientGroup.quotientMulEquivOfEq hpc.symm).symm.trans e3⟩⟩
  exact CFSG.HardMathSupport.Solomon.Proving.inputL34Cover_holds Y hq' hL3'

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
