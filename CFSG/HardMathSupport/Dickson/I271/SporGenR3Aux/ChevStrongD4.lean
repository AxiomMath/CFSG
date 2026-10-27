module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Dickson.KD
  CFSG.HardMathSupport.Dickson.DefCharOuter.Export CFSG.HardMathSupport.Solomon.Coordinator

section ChevStrongD4


theorem chevStrong_of_D4 (hD4 : D4ThreeOuterCent) : ∀ p : ℕ, ChevStrong p := by
  intro p X _ _ K B h1 h2
  have hp : p.Prime := h1.prime
  have hp2 : p ≠ 2 := h1.odd
  have hamb : ∀ q : ℕ, q.Prime → q ≠ 2 → KDAmbSolv q := fun q hq hq2 =>
    kdAmbSolv_holds hq hq2 u42_fixSubgroup_solvable
  exact chevStrong_of_residuals defCharInnerCoreFree_holds
    (defCharOuterCoreFree_of_kdata (kdOutCoreFree_of_D4 hD4) (kdOutCentInner_of_D4 hD4))
    (kd65_holds hp hp2)
    (kdChevInner_of hp hp2 (kdCharP_holds hp hp2) (hamb p hp hp2))
    (chevCentralizerStep_of_kdata
      (fun q hq hq2 => kdChevUnique_of hq hq2 (kdCharP_holds hq hq2)
        (kdOutChevUnique_of_D4 hD4 hq hq2) (hamb q hq hq2))
      (fun q hq hq2 => kdOutChev_of_D4 hD4 hq hq2)
      (kdOutExc_of_outerCent (outerCentAll_of_D4 hD4) (hamb 3 Nat.prime_three (by norm_num))))
    (chevCyclicCase_holds CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      (fun q hq hq2 => kd65_holds hq hq2))
    chevAmbCase_holds X K B h1 h2

theorem chevStrong_holds : ∀ p : ℕ, ChevStrong p :=
  chevStrong_of_D4 (d4ThreeOuterCent_of_graphCent d4ThreeGraphCent_holds)

end ChevStrongD4

end CFSG.HardMathSupport.Dickson.I271
