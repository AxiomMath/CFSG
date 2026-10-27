module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs
public import CFSG.ClassicalInvolution.SmallCases.Rank3NormalEight

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33


theorem corAStatement_of_certificates : CorAStatement :=
  fun F _ _ h S =>
    CFSG.ClassicalInvolution.exists_normal_elemAbelian_eight_of_not_fourGenerated h S

end CFSG.OddStandard.SmallF3.HarrisU33
