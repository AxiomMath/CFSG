module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U4Main

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

theorem cf67U5_thm (hGA : CFSG.Open.GriessAllModelsStatement) :
    CF67U5 :=
  cf67U5_thm_of_leaves (unLeafPlus 5) (unLeafMinus 5) hGA

end CFSG.GH74.GLS.Stage2.Bender.Thm1
