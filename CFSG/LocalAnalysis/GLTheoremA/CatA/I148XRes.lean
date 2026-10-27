module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley (TwistTag)
open CFSG.LieType.Chevalley (graphFixedRootGroup)

@[expose] def TD4InnThreeCentAt (f : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ f) ^ 3 → (∀ c, σ c = c ^ 2 ^ f) →
    ∀ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, z ^ 3 = 1 → z ≠ 1 →
      twoPart (Nat.card (Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) =
        (2 ^ f) ^ 3

@[expose] def TD4InnThreeCentLe (f : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ f) ^ 3 → (∀ c, σ c = c ^ 2 ^ f) →
    ∀ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, z ^ 3 = 1 → z ≠ 1 →
      twoPart (Nat.card (Subgroup.centralizer ({z} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) ≤
        (2 ^ f) ^ 6

end CFSG.LocalAnalysis.GLTheoremA

end
