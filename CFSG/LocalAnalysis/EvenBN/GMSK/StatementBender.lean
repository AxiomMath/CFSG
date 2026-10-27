module

public import CFSG.LocalAnalysis.SteinbergBVSp6LayerStatements
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint

@[expose] def StdUnitaryData (G : Type) [Group G] (A : Subgroup G) (n : ℕ) : Prop :=
  2 ≤ n ∧ CFSG.Open.standardComponentIsStandard A ∧ ¬ A.Normal ∧ LieModel A .PSU 3 2 n

@[expose] def StdSuzukiData (G : Type) [Group G] (A : Subgroup G) (n : ℕ) : Prop :=
  CFSG.Open.standardComponentIsStandard A ∧ ¬ A.Normal ∧ LieModel A .twistedB2 0 2 n

@[expose] def SharpOutcome (X : (D : Type) → [Group D] → Prop) (G : Type) [Group G]
    (A : Subgroup G) (t : G) : Prop :=
  haveI : (CFSG.layer G).Characteristic := CFSG.LocalCores.layer_characteristic
  SteinbergBV.OneOrTwoLayerConclusion A t ∧
    (IsSimpleGroup (CFSG.layer G) → X (CFSG.layer G) ∧
      (MulAut.conjNormal t : MulAut (CFSG.layer G)) ∉
        (MulAut.conj : CFSG.layer G →* MulAut (CFSG.layer G)).range)

end CFSG.LocalAnalysis.EvenBN.GMSK
