module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClDisp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOPc
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOOrd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClOComm

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG CFSG.Assembly.LowTwoRank

theorem oCore_holds : OCore :=
  oCore_of @false_of_pc_noE8 @false_of_psp_le_blockP @eq_two_mul_of_blockP_four
    @kappa_scalar_on_block

theorem cfQPUJClassical_holds : CFQPUJClassical :=
  cfQPUJClassical_of_core oCore_holds

end CFSG.ComponentClassification.GSThmB.QPUCl
