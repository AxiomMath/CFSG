module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Certificate8064
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
public import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Proof
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint.Chevalley (Tag adjointGroup)


theorem ext_u33_label {X : Type} [Group X] (hX : commutator X = ⊤)
    [IsSimpleGroup (X ⧸ Subgroup.center X)]
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 3 1) :
    GGHasLabel ⟨.G2der, 0, 1⟩ (X ⧸ Subgroup.center X) := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  have hC : StatedClassicalModel
      ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ .PSU 3 3 1 :=
    (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds (ZMod 2)
      hK).statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨φ⟩ := CFSG.ClassicalInvolution.Upgrade.statedClassicalModel_unique (by norm_num) h hC
  have hnab := exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance
  have : IsSimpleGroup ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ :=
    φ.symm.isSimpleGroup
  have hZ := center_eq_bot_of_isSimpleGroup_of_nonabelian (nonabelian_of_mulEquiv φ hnab)
  let ψ : CFSG.Blueprint.DerivedCentralQuotient (adjointGroup .G2 (ZMod 2)) ≃*
      ↥⁅adjointGroup .G2 (ZMod 2), adjointGroup .G2 (ZMod 2)⁆ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨e₁⟩ := centerQuot_commutator_chevGroup_equiv (ZMod 2) .G2
  unfold GGHasLabel CFSG.StandardType.LargeEvenRawDatum
  exact ⟨ZMod 2, inferInstance, inferInstance, hK, ⟨(φ.trans ψ.symm).trans e₁.symm⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
