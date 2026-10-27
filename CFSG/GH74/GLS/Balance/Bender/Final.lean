module

public import CFSG.GH74.GLS.Balance.Bender.FinalCond
public import CFSG.GH74.GLS.Balance.Bender.AuxCentral
public import CFSG.GH74.GLS.Balance.Main

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

theorem benderT511 (p : ℕ) [Fact p.Prime] : BenderT511 p :=
  benderT511_of_q42iii p bender_q42iii

theorem benderT510 (p : ℕ) [Fact p.Prime] : BenderT510 p :=
  have h52i : BenderL52i p := bender_l52i p
  have h52ii : BenderL52ii p := bender_l52ii p
  have h52iii : BenderL52iii p := bender_l52iii p
  have h52iv : BenderL52iv p := bender_l52iv p
  have h53 : BenderL53 p := bender_l53 h52i h52ii h52iii bender_q42iii
  have h54 : BenderL54 p := bender_l54 h53
  have h55 : BenderL55 p := bender_l55 h52ii h52iv h54 bender_q42iii bender_q43iii bender_q326
  have h56 : BenderL56 p := bender_l56 h55
  have h59 : BenderT59 p := bender_t59 h52iii h53 h56
  bender_t510 h52i h52ii h53 h54 h55 h56 h59

theorem benderBalance : BenderBalance :=
  benderBalance_of_q42iii bender_q42iii

theorem solvableL2PrimeBalance_proved : SolvableL2PrimeBalance :=
  solvableL2PrimeBalance_of_bender benderBalance

theorem ig_balance_fAut_solv_proved :
    CFSG.GH74.GLS.Stage1.Thm2.Recip.BalanceSolv.IG_balance_fAut_solv :=
  ig_balance_fAut_solv_of_bender benderBalance

end CFSG.GH74.GLS.Balance
