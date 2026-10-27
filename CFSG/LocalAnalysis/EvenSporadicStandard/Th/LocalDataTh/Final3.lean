module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Transv

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

section Certified


theorem thLocalWitness3_J :
    ThLocalWitness3 LocalDataTh.S LocalDataTh.A LocalDataTh.B LocalDataTh.AaJ where
  transv := LocalDataTh.transv_J
  center_quotient := LocalDataTh.center_quotient_J

theorem thLocalData3_J : ThLocalData3 J :=
  ⟨_, _, _, _, _, _, thLocalWitness_J, thLocalWitness2_J, thLocalWitness3_J⟩

theorem thLocalData3_th : ThLocalData3 (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
  ThLocalData3.of_mulEquiv (F := CFSG.Blueprint.NativeSporadic.Carrier .Th) (F' := J) thEquivJ
    thLocalData3_J

end Certified

end CFSG.EvenSporadicStandard.ThStd
