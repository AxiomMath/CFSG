module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case1Claim
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core1Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem sz32_case2_core {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}
    (hY : Sz32Case2Data Pb a c y) (hI6103 : KFactI6103Five) (hI122 : KFactI122Five)
    (hI713 : KFactI713Out) : a ∈ pCoreOf 5 (⊤ : Subgroup Y) :=
  sz32_case2_core' hY hI6103 hI122 hI713

theorem sz32_case1_claim {Y : Type} [Group Y] [Finite Y] {Pb : Subgroup Y} {a c y : Y}
    (hY : Sz32Case2Data Pb a c y) (ha : a ∈ pCoreOf 5 (⊤ : Subgroup Y)) :
    ∀ g : Y, ∀ t ∈ Pb, g * t * g⁻¹ ∈ Pb :=
  sz32_case1_claim' hY ha

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
