module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi24Glue
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi24Reps
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi24Leaf
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi24K1
public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi24WitnessCheck
public import Certificates.Certificate27750
public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24 cls_mem)
open CFSG.Sporadic.FischerOddCore (fi24D fi24U2 fi24U3)
open CFSG.ComponentClassification.M12Cover (FourClassesLarge)

attribute [local instance] CFSG.Sporadic.Fi24.rAction


theorem witFacts_of_cert :
    WitFacts fi24D ∧ WitFacts fi24U2 ∧ WitFacts fi24U3 ∧ WitFacts (fi24U2 * tR) ∧
      WitFacts (fi24U3 * tR) :=
  Certificates.certificate27750

theorem fourClassesLarge_of_facts {r : R} (hW : WitFacts r) :
    FourClassesLarge ↥(Subgroup.centralizer ({r} : Set R)) ∧
      (r ∈ JR → FourClassesLarge ↥(Subgroup.centralizer ({r} : Set R) ⊓ JR)) :=
  fourClassesLarge_of_witFacts hW
    (fun hr2 hr1 u hu hru hne => fourClassesLarge_leaf_D24 hu hr2 hru hr1 hne)
    (fun hrJ hr2 hr1 u hu hru => fourClassesLarge_leaf_D24_J hu hrJ hr2 hru hr1)

theorem hypothesisOne_fi24Prime :
    CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) := by
  obtain ⟨h0, h1, h2, h1T, h2T⟩ := witFacts_of_cert
  have c0 := fourClassesLarge_of_facts h0
  have c1 := fourClassesLarge_of_facts h1
  have c2 := fourClassesLarge_of_facts h2
  have c1T := fourClassesLarge_of_facts h1T
  have c2T := fourClassesLarge_of_facts h2T
  refine hypothesisOne_carrier_fi24prime_of_leaves (fourClassesLarge_J_of_reps ?_)
    (fourClassesLarge_R_of_reps ?_)
  · intro r hr
    rcases hr with rfl | rfl | rfl
    · exact c0.2 fi24D_mem_JR
    · exact c1.2 fi24U2_mem_JR
    · exact c2.2 fi24U3_mem_JR
  · intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact c0.1
    · exact c1.1
    · exact c2.1
    · exact fourClassesLarge_centralizer_tR
    · obtain ⟨k, hk⟩ := CFSG.Sporadic.Fi24.exists_cls
        CFSG.Sporadic.FischerOddCore.fi24D_mul_tR_mem
      rw [← hk]
      exact fourClassesLarge_centralizer_D24 (cls_mem _)
    · exact c1T.1
    · exact c2T.1

end CFSG.EvenSporadicStandard.YS14

end
