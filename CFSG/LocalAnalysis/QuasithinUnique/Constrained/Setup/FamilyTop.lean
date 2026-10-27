module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAssembly
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddClassical
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyPrimeSquare
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOneGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Component
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Graph
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyAltLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiComponent
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassicalProp
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate43
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3084
public import Certificates.Certificate3086
public import Certificates.Certificate3119
public import Certificates.Certificate3120
public import Certificates.Certificate3139
public import Certificates.Certificate3167
public import Certificates.Certificate3168
public import Certificates.Certificate3172
public import Certificates.Certificate8010
public import Certificates.Certificate8011
public import Certificates.Certificate8012
public import Certificates.Certificate8013
public import Certificates.Certificate8014
public import Certificates.Certificate8015
public import Certificates.Certificate8016
public import Certificates.Certificate8017
public import Certificates.Certificate8018
public import Certificates.Certificate8019
public import Certificates.Certificate8020
public import Certificates.Certificate8021
public import Certificates.Certificate8022
public import Certificates.Certificate8024
public import Certificates.Certificate8025
public import Certificates.Certificate8026
public import Certificates.Certificate8027
public import Certificates.Certificate8028
public import Certificates.Certificate8029
public import Certificates.Certificate8030
public import Certificates.Certificate8031
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PureSemilinear
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.QuasithinUnique.Setup.X35

theorem familyTop
    (hlayer : ActorLayerProp) (hT : ActorComponentTransfer)
    (hTrans : X1.ComponentTransferProp) (hSec : X1.IrreducibleSectionProp)
    (hspor : NoSporadicComponentProp) (hsec : SectionProductionProp)
    (hlin3 : PrimeLinearThreeExclusionProp)
    (huni3 : PrimeUnitaryThreeExclusionProp) : OneQuasisimpleResidualProp := by
  have hGL3 : NoGL3ComponentProp := noGL3Component hlayer hT hTrans gl3GraphNormalizerExclusion
  have hA78 : NoAlt78BinaryLinearProp := noAlt78BinaryLinear hT hGL3
  have hSuz : NoSuzukiComponentProp := noSuzukiComponent hlayer hsec
  have hodd : OddClassicalSmallProp :=
    oddClassicalSmall CFSG.SectionRank.catalogStepHyp hlayer hTrans hSec hA78 hlin3 huni3
      primeSquareExclusion
  have hfam : FamilyRestrictionProp := familyRestriction hlayer hspor hSuz hA78 hodd
  exact oneQuasisimpleResidual hlayer hfam
    (componentOddRankTwoNormal CFSG.SectionRank.oddKernelCentralization
      CFSG.SectionRank.catalogStepHyp)
    oddRankOneOddClassical CFSG.QuasithinUnique.Vol2Native.EvenWit.oddRankOneEvenClassical
    oddRankOneChevalley oddRankOneReeTits trialityTwoHasRankTwo

end CFSG.QuasithinUnique.Setup.Family
