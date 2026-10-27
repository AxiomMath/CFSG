module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenExc
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

@[expose] def UnitaryEvenInnerTwoPart : Prop :=
  ∀ (f : ℕ) (K' : Type) [Field K'] (h : UnitaryFieldData 2 f K') (n : ℕ), 3 ≤ n →
    ∀ y : unitaryPSU h (2 * n), orderOf y = 2 →
      f * (n ^ 2 + 2) ≤
        (Nat.card (centralizer ({y} : Set (unitaryPSU h (2 * n))))).factorization 2

end CFSG.SeitzReduction.SymplecticPilot
