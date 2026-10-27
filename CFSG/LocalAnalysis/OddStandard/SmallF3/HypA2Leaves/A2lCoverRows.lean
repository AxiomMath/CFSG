module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverL3U3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverL4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverU4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverSp4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SLTwoDatum

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ComponentClassification

@[expose] def a2lCoverOn (P : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K → IsPGroup 2 ↥(center K) → center K ≠ ⊥ →
    P (K ⧸ center K) → HypA2.CentralDatum K

structure a2lCoverSpin : Prop where
  o73 : a2lCoverOn fun S _ => LieModel S .POmegaOdd 3 3 1
  oPlus43 : a2lCoverOn fun S _ => LieModel S .POmegaPlus 4 3 1
  oMinus43 : a2lCoverOn fun S _ => LieModel S .POmegaMinus 4 3 1

theorem a2l_coverDatum_of_rows (hGr : TBLit.GriessMultipliersOdd) (hC : HypA2.ChevOddInChev2)
    (hSpin : a2lCoverSpin) : HypA2.CoverDatum := by
  intro K _ _ hq h2 hZ hS hnF
  rcases hS with h | h | h | h | h | h | h | h | h | h
  · exact HypA2.centralDatum_of_psl_two hGr hq h2 hZ Nat.prime_three (by norm_num)
      (by norm_num) h
  · exact HypA2.centralDatum_of_psl_two hGr hq h2 hZ Nat.prime_three (by norm_num)
      (by norm_num) h
  · exact (a2l_false_psl33 hq h2 hZ h).elim
  · exact (a2l_false_psu33 hq h2 hZ h).elim
  · exact a2l_centralDatum_psp43 hq h2 hZ h
  · exact a2l_centralDatum_psl43 hC hq h2 hZ h
  · exact a2l_centralDatum_psu43 hC hq h2 hZ hnF h
  · exact hSpin.o73 K hq h2 hZ h
  · exact hSpin.oPlus43 K hq h2 hZ h
  · exact hSpin.oMinus43 K hq h2 hZ h

end CFSG.OddStandard.SmallF3.HypA2Leaves
