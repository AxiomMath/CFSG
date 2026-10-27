module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Case2G
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Quot

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (normalizes_of_quotient_normal)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_normal_core (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hSz : Sz32Facts)
    (hSz' : Sz32OpenFacts) (hI6103 : KFactI6103Five) (hI122 : KFactI122Five) (hI713 : KFactI713Out)
    (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G} (hP : Sz32Struct P x J a c y)
    (hL : Sz32Lines P x (a ^ 5)) (hZ : Sz32ZFacts P M x (a ^ 5)) :
    M ≤ Subgroup.normalizer ((P : Subgroup G) ⊔ rankThreePrimeCore 5 M : Subgroup G) := by
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  obtain ⟨N, hN⟩ := sz32_centSeries hS hD1 hU0 hSz hSz' hc hP
  have hpres := hP.pres_P
  have hdat := sz32_case2_G hS hD1 hU0 hc hP hL hZ hN (hPM hpres.a_mem) (hPM hpres.c_mem)
    (hPM hpres.y_mem)
  have hcore := sz32_case2_core hdat hI6103 hI122 hI713
  have hnorm := sz32_case1_claim hdat hcore
  exact normalizes_of_quotient_normal hPM hnorm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
