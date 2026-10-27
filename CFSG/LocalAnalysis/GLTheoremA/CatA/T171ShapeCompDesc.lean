module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLift
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.ClassicalGroups
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import Certificates.Certificate10
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalCores CFSG.ComponentClassification.FixedCommutingProduct
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev piCenterQuot {R : Type} [Group R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    ↥L →* R :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))

abbrev centralizerInL (d : G) : Subgroup ↥L :=
  (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L

theorem mem_centralizerInL {d : G} {x : ↥L} :
    x ∈ centralizerInL (L := L) d ↔ d⁻¹ * (x : G) * d = x := by
  constructor
  · intro hx
    have hx' := (Subgroup.mem_subgroupOf.mp hx)
    have hc : d * (x : G) = (x : G) * d :=
      Subgroup.mem_centralizer_iff.1 hx'.2 d (Set.mem_singleton d)
    calc d⁻¹ * (x : G) * d = d⁻¹ * ((x : G) * d) := by group
      _ = d⁻¹ * (d * (x : G)) := by rw [hc]
      _ = (x : G) := by group
  · intro hx
    refine Subgroup.mem_subgroupOf.mpr ⟨x.2, ?_⟩
    change (x : G) ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x : G) * d = d * (d⁻¹ * (x : G) * d) := by group
      _ = d * (x : G) := by rw [hx]

@[expose] def ComponentDescent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.Open.IsQuasisimple ↥L →
    ∀ (R : Type) [Group R] [Finite R]
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (d : G)
      (_ : d ∈ Subgroup.normalizer (L : Set G)) (φ : MulAut R),
      LargeEvenInduces θ (conjRel d) φ →
      ∀ (J : Subgroup G),
        CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) →
        LargeEvenLayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J →
        CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ)) (fixedSubgroup φ) ∧
          LargeEvenLayer (fixedSubgroup φ) = (J.subgroupOf L).map (piCenterQuot θ)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
