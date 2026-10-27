module

public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

@[expose] def NoIntrinsicSLTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ¬ Catalog G → ∀ {u : G}, orderOf u = 2 → ∀ {J : Subgroup G},
    HarrisLit.IsTwoComponentIn J (centralizer {u}) → u ∈ J → ∀ {p k : ℕ}, p.Prime → p ≠ 2 →
      HarrisLit.IsSLTwoOver (p ^ k) (↥J ⧸ pPrimeCore 2 ↥J) → False

@[expose] def ClassicalTwoComponentOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ∀ {z : X}, orderOf z = 2 → ∀ {J : Subgroup X}, J ≤ centralizer ({z} : Set X) →
    IsPComponent 2 (J.subgroupOf (centralizer ({z} : Set X))) → z ∈ J →
      CFSG.pRank 2 J ≤ 1 → OddLieType X

@[expose] def ChevOddInChev2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (r : ℕ), r.Prime → r ≠ 2 →
    HarrisLit.IsSimpleChevalleyOver r S → GH74.GLS.InChev2 S →
      Nat.card S ∈ ({60, 168, 6048} : Finset ℕ) ∨ LieModel S .PSL 2 3 2 ∨ LieModel S .PSp 2 3 1

structure Phase1Inputs : Prop where
  dPrime : GS82PumpInputs.TheoremDPrime
  p1 : GS82PumpInputs.ChevOddPumpLeaf
  p2 : GS82PumpInputs.ChevOddCentralPumpInput
  p4 : GS82PumpInputs.MTypeOfSLTwoSection
  p5 : GS82PumpInputs.AltCentralPumpInput
  p7 : GS82PumpInputs.SLTwoCentralPumpInput
  p8 : GS82PumpInputs.SpFourThreeCentralPumpInput
  p11 : GS82PumpInputs.L34CentralSLTwoFact
  griess : TBLit.GriessMultipliersOdd
  schur : SolAltLit.SchurAlternatingMultiplierInput
  solomon : GSThmB.Solomon2AnInput
  harris : HarrisLit.Harris82Theorem1SimpleKProperOdd
  noSL2 : NoIntrinsicSLTwo
  classical : ClassicalTwoComponentOdd
  chevOdd : ChevOddInChev2

end CFSG.OddStandard.SmallF3.HypA2
