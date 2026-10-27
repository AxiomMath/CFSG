module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6d
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6e
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11U62Rank
public import Certificates.Data.U62Rank.Check

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Fischer CFSG.StandardType CFSG.Assembly
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem m6Main : M6Main := by
  intro B ⟨c, hc⟩ hns hq
  by_cases h3 : (B : GL (Fin 6) F4) ^ 3 = 1
  · exact U4InnU6.pPrimeCore_CenD_cube_one B (Subtype.ext h3) hns hq
  · exfalso
    obtain ⟨L, hLC, hLp, hLd⟩ := hq
    have hc1 : c ≠ 1 := fun h => h3 (by rw [hc, h, map_one])
    have h504 := U4InnU6.perfect_card_nine B hc1 hc hLC hLp
    have := hLd.trans h504
    norm_num at this

theorem u4InnAt_u6two : U4InnAt S9.isU6two := by
  intro S _ _ hcat
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := U62RankSound.lieIndex_isU6two hcat
  obtain ⟨e'⟩ := bridge_u6two_stated hv hq e
  exact U4InnModel.of_mulEquiv e' (u4InnModel_S6_of m6Main)

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
