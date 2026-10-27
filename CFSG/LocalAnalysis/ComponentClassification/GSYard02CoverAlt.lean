
module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverAltBase

public import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverGH
public import Certificates.Certificate13001
public import Certificates.Certificate13002
public import Certificates.Certificate13003
public import Certificates.Certificate13004

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup CFSG.Alternating.Multipliers.Spin
open SpinNative (Wd Q4 invW wordsOK)
open CFSG.Alternating.Multipliers CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.Sol76.Sig.GSYard02.CoverAltGroup
open scoped commutatorElement

theorem coverLeafAlt_holds :
    CoverLeafAlt := by
  intro Q _ _ hQ n hn8 hn11 hQA
  obtain ⟨eQ⟩ := hQA
  obtain ⟨hquasi, hz, h2, -, -, -⟩ := hQ
  interval_cases n
  · exact sylowFourJoined_of_cover hquasi hz h2 (m := 6) (by norm_num) eQ
      Certificates.certificate13001
  · exact sylowFourJoined_of_cover hquasi hz h2 (m := 7) (by norm_num) eQ
      Certificates.certificate13002
  · exact sylowFourJoined_of_cover hquasi hz h2 (m := 8) (by norm_num) eQ
      Certificates.certificate13003
  · exact sylowFourJoined_of_cover hquasi hz h2 (m := 9) (by norm_num) eQ
      Certificates.certificate13004

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
