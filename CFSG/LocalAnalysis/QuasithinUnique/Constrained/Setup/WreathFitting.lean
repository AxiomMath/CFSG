module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

theorem solvable_fitting_self_centralizing {U : Type*} [Group U] [Finite U]
    (hU : Group.IsSolvable U) :
    Subgroup.centralizer (CFSG.fittingSubgroup U : Set U) ≤ CFSG.fittingSubgroup U :=
  CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hU

end CFSG.QuasithinUnique.Setup.Wreath
