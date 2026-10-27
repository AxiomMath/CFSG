module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Proofs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2Q
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2StageD
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2List
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage8
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage9
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9Insp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage10
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma27A5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Final
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppC56A5
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
public import Certificates.Certificate110
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public import Certificates.Certificate2195
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2199
public import Certificates.Certificate2202
public import Certificates.Certificate2204
public import Certificates.Certificate2262
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2270
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3120
public import Certificates.Certificate3157
public import Certificates.Certificate4041
public import Certificates.Certificate4047
public import Certificates.Certificate4065
public import Certificates.Certificate4074
public import Certificates.Certificate4078
public import Certificates.Certificate8033
public import Certificates.Certificate4119
public import Certificates.Certificate4121
public import Certificates.Certificate4139
public import Certificates.Certificate4145
public import Certificates.Certificate17017
public import Certificates.Certificate17029
public import Certificates.Certificate17037
public import Certificates.Certificate17027
public import Certificates.Certificate5952
public import Certificates.Certificate12952
public import Certificates.Certificate14951
public import Certificates.Certificate3950
public import Certificates.Certificate4035
public import Certificates.Certificate17030
public import Certificates.Certificate3951

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.A5

theorem lemma2_4_25_of_inputs (hC54s2 : LemmaC54_3_s2) (hC56s2 : LemmaC56_14_s2)
    (h567 : Lemma245_C56_7) (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hP1 : CompChi0Block) (hP2 : NoProperA5Block) (hComp : Comp25Component)
    (hlist115 : Lemma115_3_List) (hTab : TabKc3) (hKc3 : Kc3Inspection) : Lemma2_4_25 :=
  lemma2_4_25_of_steps (lemma2_4_25_0_of lemma245_C55 (lemma2_4_25_Q hC54s2 h567))
    (lemma2_4_25_A hC54s2 h567 hC56s2) (lemma2_4_25_B hC54s2 h567 h37 h39 hP1 hP2)
    (lemma2_4_25_C hC54s2 h567 h37 h39 hP1 hP2 hComp (comp25List_of hlist115 hTab))
    (lemma2_4_25_D hKc3)

theorem a5BlockExcluded
    (h246 : Lemma246Chi)
    (h245_4 : Lemma245_4) (hC54 : LemmaC54_3) (h314 : A314A5Excluded)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hP1 : CompChi0Block) (hComp : Comp25Component)
    (hlist115 : Lemma115_3_List) (hTab : TabKc3) (hKc3 : Kc3Residual)
    (hSA : ConstrainedSetupAt) (hlin : Lin2BlockExcluded) (ha3 : SingleA3Excluded)
    (hP121 : Id2519.Prop121Three) (h2397 : Lemma2_3_9_7W) : A5BlockExcluded :=
  have h25 : Lemma2_4_25 :=
    lemma2_4_25_of_inputs AppCS2.lemmaC54_3_s2 AppCS2.lemmaC56_14_s2
      (lemma245_C56_7 AppC.c56A5Case AppCS2.c56DoubleCase) h37 h39 hP1 G3.noProperA5Block hComp
      hlist115 hTab
      (kc3Inspection_of_residual hKc3)
  have h247 : DoubleA3.Lemma2_4_27 := DoubleA3.lemma2_4_27_of hSA hlin ha3 h25
  a5BlockExcluded_of_steps h25
    (lemma2_4_29_1 h247 h245_4 hC54 h314) (lemma2_4_29_2 h247 h245_4 hC54 h314)
    (lemma2_4_29_3 h247 h245_4 hC54 h314) (lemma2_4_29_4 h247 h245_4 hC54 h314)
    (lemma2_4_29_5 h247 h246) (lemma2_4_29_6 h247 h245_4 hC54 h314)
    (lemma2_4_29_7 h247 h245_4 hC54 h314)
    (lemma2_4_29_8 h247 h245_4 hC54 h314 h25 hSA hlin ha3)
    (lemma2_4_29_9 h247 h245_4 hC54 h314 hP121 h2397
      (lemma2_4_29_9_K_proved h247 h245_4 hC54 h314 hP121)) (lemma2_4_29_10 h247 h245_4 hC54 h314)
    lemma2_4_29_11

end CFSG.QuasithinUnique
