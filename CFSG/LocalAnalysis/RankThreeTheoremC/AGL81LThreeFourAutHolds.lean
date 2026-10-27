module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutModel
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutGSp
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutFive
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutLocal
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open AutSection

theorem kFactLThreeFourAutSection_holds : KFactLThreeFourAutSection := by
  intro q hq hq2 hq3 V _ _ hV hr A K _ hK φ hφ
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨W, _, _, _, ρ, hker, h3 | ⟨h4, B, hB, halt, hsim⟩⟩ := hasSmallSympModel hq2 hV hr
  · exact not_surjective_of_dim_le_three hq2 (fiveCentralizesTwo hq2) h3 ρ hker A
      (lThreeFourTwoLocal_of hK) φ hφ
  · exact not_surjective_of_symp hq3 (similitudeThreeAbelian hq2 hq3) h4 ρ hker B hB halt hsim A
      (lThreeFourThreeLocal_of hK) φ hφ

end CFSG.LocalAnalysis.RankThreeTheoremC
