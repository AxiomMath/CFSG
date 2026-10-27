module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieReduce
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLiftRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLiftGood
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreAll
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreY1
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreY2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieBS
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieAmb
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LiePL
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieMult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie


theorem kd264KLie_holds (hI : KD264LieInputs) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    KD264KLie p := by
  have hBS : ∀ r : ℕ, r.Prime → r ≠ 2 → KD264BS r := fun r hr hr2 =>
    kd264BS_of_excNoGood hr hr2 (kd264ExcNoGood_holds hI hr hr2 (kd264PL_holds r hr hr2))
  have hY1 : KD264CaseY1 :=
    kd264CaseY1_holds hI (hBS 3 Nat.prime_three (by decide))
      (kd264Amb_holds 3 Nat.prime_three (by decide))
  exact kd264KLie_of_coreS hp hp2 (fun Y _ _ => lBalanceAt_holds Y p hp)
    (listedMultiplierBound_of_tables
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
      sporadicMultiplierTable_holds p)
    (hatOddMultiplierBound_of_tables sporadicMultiplierTable_holds)
    (kd264CoreS_holds hI (kd264PL_holds p hp hp2) (hBS p hp hp2) (kd264Amb_holds p hp hp2) hY1
      (kd264CaseY2_holds hI))
    (kd264LiftGood_holds hp) (kd264LiftLow_holds hI.i5Low hp hp2)
    (kd264LiftNoMult_holds hp hp2 (kd264MultLie_holds p hp hp2))
    (kd264LiftField_holds hI.i5Field hp) (kd264LiftMRJ_holds hI.i5Low hp hp2)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
