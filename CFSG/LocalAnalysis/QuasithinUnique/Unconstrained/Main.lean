module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Assembly
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_5
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_10
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Out
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_13
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_18
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.M11NotBender
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_23
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2Small
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Main
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19L2pGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Final
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsK33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsL33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinCore
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_22
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_24
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_25
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26Claim
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_27
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_Final
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.BadCaseLocal
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate43
public import Certificates.Certificate110
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public import Certificates.Certificate4041
public import Certificates.Certificate4051
public import Certificates.Certificate4144
public import Certificates.Certificate4145
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique

theorem unconstrainedBranch_of_remaining_parts
    (h252 : Lemma252) (h253 : Lemma253Component)
    (hemb : Lemma256Embedding) (ha312 : A312Sublist) (h257 : Lemma257) (h258 : Lemma258)
    (hK33 : K33LocalFacts) (hL33 : L33AutFacts) (hA6 : A6OuterTypes)
    (h2519 : Lemma2519)
    (h2521 : Lemma2521) (h2522 : Lemma2522) (h2524 : Lemma2524)
    (h2525 : Lemma2525) (h2526 : Lemma2526) (h2527 : Lemma2527) (hfinal : Lemma25Final) :
    UnconstrainedBranch :=
  unconstrainedBranch_of_parts h252 h253 notation254 lemma255 (lemma256_of_inputs h252 hemb ha312
      m11OutTrivial m11A6Normalizer)
    h257 h258 lemma2510 lemma2511 lemma2512 lemma2513 (lemma2515 hK33 hL33 m11OutTrivial)
    (lemma2516 hA6)
    (lemma2518 ⟨h252, notation254, lemma255, lemma256_of_inputs h252 hemb ha312 m11OutTrivial
        m11A6Normalizer, h257, h258,
      lemma2510, lemma2511, lemma2512, lemma2513⟩ (lemma2515 hK33 hL33 m11OutTrivial)
      m11_not_fusionIsBenderGroup)
    h2519 (lemma2520 l2pFacts) h2521 h2522 lemma2523 h2524 h2525 h2526 h2527 hfinal

end CFSG.QuasithinUnique
