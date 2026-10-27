module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedW
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM11
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL42
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239Covers
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
public import Certificates.Certificate110
public import Certificates.Certificate2197
public import Certificates.Certificate3120
public import Certificates.Certificate9121
public import Certificates.Certificate4086
public import Certificates.Certificate9214
public import Certificates.Kernel.J4Count.FixCE
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.QuasithinUnique.Vol2Native

open CFSG.Open CFSG.Quasithin

theorem lemma2_3_9_7_listedW_of_remaining_inputs
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hl42 : L239.L239L42Overgroups)
    (hm22 : L239.L239M22Parabolic) (hm23 : L239.L239M23Parabolic) (hcov : L239.L239Covers) :
    Lemma2_3_9_7_listedW :=
  lemma2_3_9_7_listedW_of_inputs h37 h38 h238 hlist hnot hpairs hl42 L239.l239L33Overgroups
    L239.l239M11Overgroups hm22 hm23 hcov

theorem lemma2_3_9_7W_of_remaining_inputs
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hl42 : L239.L239L42Overgroups)
    (hm22 : L239.L239M22Parabolic) (hm23 : L239.L239M23Parabolic) (hcov : L239.L239Covers) :
    Lemma2_3_9_7W :=
  lemma2_3_9_7W_of_listedW hlist
    (lemma2_3_9_7_listedW_of_remaining_inputs h37 h38 h238 hlist hnot hpairs hl42 hm22 hm23 hcov)

theorem lemma2_3_9_7_listedW_of_open_inputs
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hm22 : L239.L239M22Parabolic)
    (hm23 : L239.L239M23Parabolic) (hcov : L239.L239Covers) :
    Lemma2_3_9_7_listedW :=
  lemma2_3_9_7_listedW_of_remaining_inputs h37 h38 h238 hlist hnot hpairs L239.l239L42Overgroups hm22
    hm23 hcov

theorem lemma2_3_9_7W_of_open_inputs
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hm22 : L239.L239M22Parabolic)
    (hm23 : L239.L239M23Parabolic) (hcov : L239.L239Covers) :
    Lemma2_3_9_7W :=
  lemma2_3_9_7W_of_remaining_inputs h37 h38 h238 hlist hnot hpairs L239.l239L42Overgroups hm22 hm23
    hcov

theorem lemma2_3_9_7_listedW_of_open_inputs'
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hm22 : L239.L239M22Parabolic)
    (hm23 : L239.L239M23Parabolic) :
    Lemma2_3_9_7_listedW :=
  lemma2_3_9_7_listedW_of_open_inputs h37 h38 h238 hlist hnot hpairs hm22 hm23 L239.l239Covers

theorem lemma2_3_9_7W_of_open_inputs'
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h238 : Lemma2_3_8_4) (hlist : Lemma115_3_List) (hnot : L239.L239NotRankOne)
    (hpairs : L239.L239ParabolicPairs) (hm22 : L239.L239M22Parabolic)
    (hm23 : L239.L239M23Parabolic) :
    Lemma2_3_9_7W :=
  lemma2_3_9_7W_of_open_inputs h37 h38 h238 hlist hnot hpairs hm22 hm23 L239.l239Covers

end CFSG.QuasithinUnique.Vol2Native
