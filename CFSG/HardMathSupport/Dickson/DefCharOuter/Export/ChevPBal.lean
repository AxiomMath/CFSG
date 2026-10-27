module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.KData
public import CFSG.HardMathSupport.Dickson.I271.ChevPBalOuter
public import CFSG.HardMathSupport.Dickson.I271.ChevAmb
public import CFSG.HardMathSupport.Dickson.I271.ChevCyclic
public import CFSG.HardMathSupport.Dickson.KD.CharP
public import CFSG.LocalAnalysis.GLTheoremA.S3.KDChev
public import CFSG.LocalAnalysis.GLTheoremA.S3.KD65Holds
public import CFSG.LocalAnalysis.GLTheoremA.S3.KDAmbSolv
public import CFSG.HardMathSupport.Solomon.Coordinator.I19DefCharHolds

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.KD CFSG.HardMathSupport.Solomon.Coordinator

theorem i271ChevPBal_of_open
    (hO : OuterCentAll) (hNine : KDU43NineFold) : I271ChevPBal := by
  have hamb : ∀ p : ℕ, p.Prime → p ≠ 2 → KDAmbSolv p := fun p hp hp2 =>
    kdAmbSolv_holds hp hp2 u42_fixSubgroup_solvable
  exact i271ChevPBal_of_kdata defCharInnerCoreFree_holds (kdOutCoreFree_of_outerCent hO)
    (kdOutCentInner_of_outerCent hO) (fun p hp hp2 => kd65_holds hp hp2)
    (fun p hp hp2 => kdChevInner_of hp hp2 (kdCharP_holds hp hp2) (hamb p hp hp2))
    (fun p hp hp2 => kdChevUnique_of hp hp2 (kdCharP_holds hp hp2)
      (kdOutChevUnique_of_outerCent hO hp hp2) (hamb p hp hp2))
    (fun p hp hp2 => kdOutChev_of_outerCent hO hp hp2)
    (kdOutExc_of_outerCent hO (hamb 3 Nat.prime_three (by norm_num)))
    (chevCyclicCase_of_nineFold CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      (fun p hp hp2 => kd65_holds hp hp2) hNine)
    chevAmbCase_holds

theorem i271ChevPBal_of_outerCent
    (hO : OuterCentAll) : I271ChevPBal :=
  i271ChevPBal_of_open hO kdU43NineFold_holds

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
