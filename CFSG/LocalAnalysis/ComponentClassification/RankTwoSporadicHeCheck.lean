module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHe
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHeMultiplier
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import Certificates.Certificate15005
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Exc
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.He

open CFSG CFSG.Sporadic.HeldB

theorem he_yCensusII_cert :
    YCensus (heP.subgroupOf heAutGroup) (· ≤ heP.subgroupOf heAutGroup) :=
  Certificates.certificate15005.1

theorem he_yCensus17U_cert :
    YCensus17U (heP.subgroupOf heAutGroup) (fun _ => False) :=
  Certificates.certificate15005.2

theorem sporadicCaseOdd_He
    (hM : CFSG.Monster.Schur.NoPerfectDoubleCover (Blueprint.NativeSporadic.Carrier .He))
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .He :=
  sporadicCaseOdd_of_yCensus17U h32 h33 (oddMultiplier_of_noPerfectDoubleCover hM) heAutModel
    he_commutator_le he_yCensusII_cert he_yCensus17U_cert

theorem sporadicCaseOdd_He_of_lemmas
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .He :=
  sporadicCaseOdd_He
    (noPerfectDoubleCover_He Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate)
    h32 h33

theorem not_isSporadic_He_of_lemmas
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} (hH : RankTwoStandard.RankTwoHyp G A) :
    ¬ Blueprint.NativeSporadic.IsSporadic (RankTwoStandard.rankTwoQuot A) .He :=
  not_isSporadic_of_sporadicCaseOdd (sporadicCaseOdd_He_of_lemmas h32 h33) hH

end CFSG.ComponentClassification.RankTwoSporadic.He
