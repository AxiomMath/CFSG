module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.JMaxDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def B_pumpupStepAt (d : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Gen4 G → KGH G →
    ∀ (x t : G) (M M' : Subgroup G), GLS.PumpUpLT 2 x M t M' →
      InG2Depth d (↥M ⧸ pPrimeCore 2 ↥M) →
        GLS.InG2 (↥M' ⧸ pPrimeCore 2 ↥M') ∧
          (d2 (↥M' ⧸ pPrimeCore 2 ↥M') < d ∨
            (d2 (↥M' ⧸ pPrimeCore 2 ↥M') = d ∧
              FRank (↥M ⧸ pPrimeCore 2 ↥M) < FRank (↥M' ⧸ pPrimeCore 2 ↥M')) ∨
            Nonempty ((↥M' ⧸ pPrimeCore 2 ↥M') ≃* (↥M ⧸ pPrimeCore 2 ↥M)))

@[expose] def B_S3_pumpupStep : Prop := B_pumpupStepAt 7

end CFSG.GH74.Generic.S3
