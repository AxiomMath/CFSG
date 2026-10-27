module

public import CFSG.GH74.GLS.Balance.Reduce
public import CFSG.GH74.GLS.Balance.Step3
public import CFSG.GH74.GLS.Balance.SolvComp
public import CFSG.GH74.GLS.Balance.Lift

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

theorem solvableL2PrimeBalance_of_bender (hB : BenderBalance) : SolvableL2PrimeBalance :=
  solvableL2PrimeBalance_of_core fun X _ _ hO x hx V hV => by
    obtain ⟨A⟩ := solvAPI_of_isSolvTwoCompSL23In hV
    exact core_balance hB hO hx A

theorem ig_balance_fAut_solv_of_bender (hB : BenderBalance) :
    CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv.IG_balance_fAut_solv :=
  ig_balance_fAut_solv_of (solvableL2PrimeBalance_of_bender hB)

end CFSG.GH74.GLS.Balance
