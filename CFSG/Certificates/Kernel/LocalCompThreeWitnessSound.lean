module

public import Certificates.Data.Kernel.LocalComp.ThreeW
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
import CFSG.Certificates.Kernel.LocalComp.Spec.ThreeW

public section

namespace CFSG.KC.LocalComp.ThreeW

open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
open CFSG.KC.LocalComp.Spec

private theorem witnessCoreK_eq_witnessCore (n : Nat) (gens gensInv : Array Table) (S : Array Table)
    (y : Table) :
    witnessCoreK n gens gensInv S y =
      CFSG.ComponentClassification.RestrictedStd.Spor.witnessCore n gens gensInv S y := by
  simp only [witnessCoreK, CFSG.ComponentClassification.RestrictedStd.Spor.witnessCore,
    tblEqK_eq_tblEq, commTK_eq_commT, ordTestK_eq_ordTest]

private theorem threeWitnessK_eq_threeWitnessOK (n : Nat) (gens gensInv : Array Table) (q y : Table)
    (cap : Nat) :
    threeWitnessK n gens gensInv q y cap =
      CFSG.ComponentClassification.RestrictedStd.Spor.threeWitnessOK n gens gensInv q y cap := by
  simp only [threeWitnessK, CFSG.ComponentClassification.RestrictedStd.Spor.threeWitnessOK,
    conjClosureL_eq_conjClosure, conjTreeOKK_eq_conjTreeOK, witnessCoreK_eq_witnessCore]

theorem threeWitnessOK_of_K {n : Nat} {gens gensInv : Array Table} {q y : Table} {cap : Nat}
    (h : threeWitnessK n gens gensInv q y cap = true) :
    CFSG.ComponentClassification.RestrictedStd.Spor.threeWitnessOK n gens gensInv q y cap =
      true := by
  rw [← threeWitnessK_eq_threeWitnessOK]
  exact h

theorem threeWitnessOK_of_K_eq {n : Nat} {gens gensInv G GI : Array Table} {q y Q Y : Table}
    {cap : Nat} (hg : gens = G) (hgi : gensInv = GI) (hq : q = Q) (hy : y = Y)
    (h : threeWitnessK n G GI Q Y cap = true) :
    CFSG.ComponentClassification.RestrictedStd.Spor.threeWitnessOK n gens gensInv q y cap =
      true := by
  subst hg hgi hq hy
  exact threeWitnessOK_of_K h

end CFSG.KC.LocalComp.ThreeW

end
