module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.AaCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalData2Basic

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

section Certified

theorem thLocalWitness2_J :
    ThLocalWitness2 LocalDataTh.B LocalDataTh.A LocalDataTh.AaJ LocalDataTh.bAa :=
  ThLocalWitness2.of_basic thLocalWitness_J (LocalDataTh.AaJ_le_B LocalDataTh.aaRel)
    (LocalDataTh.AaJ_comm LocalDataTh.aaRel) (LocalDataTh.card_AaJ LocalDataTh.aaRel)
    (LocalDataTh.AaJ_exp LocalDataTh.aaRel) (LocalDataTh.A_eq_sq_AaJ LocalDataTh.aaRel)
    (LocalDataTh.bAa_mem_B LocalDataTh.aaRel) (LocalDataTh.bAa_not_mem LocalDataTh.aaRel)
    (LocalDataTh.bAa_sq LocalDataTh.aaRel) (LocalDataTh.bAa_inv LocalDataTh.aaRel)

end Certified

end CFSG.EvenSporadicStandard.ThStd
