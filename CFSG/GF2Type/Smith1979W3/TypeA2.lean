module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.TimmesfeldLargeExtraspecialMilestoneDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32NSp4Over

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification

@[expose] def T1216WidthThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
    S.width = 3 → ¬ S.IsReducible →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g) →
        (¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) ∧
          ∃ q : QuadraticForm (ZMod 2) (Fin (2 * S.width) → ZMod 2),
            timmesfeldNondegenerate q ∧ ¬ timmesfeldPlusType q ∧
              (Nonempty (S.Mbar ≃* timmesfeldOmega q) ∨
                Nonempty (S.Mbar ≃* timmesfeldIsometries q))

end CFSG.GF2Type.Smith1979W3
