module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Chain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigAsm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Red2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L111N
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L112
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2P
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L127
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8Split
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModNoL216
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModNoL34
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5L128
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129J
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210N
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Prince
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12FusX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Hyp62
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L119
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111X
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SPocket

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Inputs11 : Prop where
  type1110 : Asc82Step1110Type
  single1110 : Asc82Step1110Single
  dihSd : Asc82InputDihSd
  kBigSD : Asc82Step1111KBigSD

structure Asc82Inputs128 : Prop where
  s8Dich : Asc82S8Dich

structure Asc82Omega5Inputs : Prop extends Asc82Omega5Inputs10, Asc82Inputs11,
    Asc82Inputs128 where
  l63 : Asc82Lemma63
  l65 : Asc82Lemma65
  z4out : Asc82StepZ4Out
  z2a5 : Asc82Z2A5K
  split5 : Asc82FactSplit5
  zExists : Asc82ZExists

theorem asc82Pre11_of_inputs (i : Asc82Omega5Inputs) : Asc82Pre11 :=
  asc82Pre11_of_inputs10 i.toAsc82Omega5Inputs10

theorem asc82Res11_of_pre (hp : Asc82Pre11) (i : Asc82Inputs11) : Asc82Res11 := by
  have h111N := asc82Lemma111N_of hp (asc82Step111T_of hp)
  have h112 := asc82Lemma112_of hp h111N
  have h113 := asc82Lemma113_of hp
  have h114 := asc82Lemma114_of hp h112
  have h115b := asc82Lemma115b_of hp h112
  have h115c := asc82Lemma115c_of hp
  have h115d := asc82Lemma115d_of hp h112
  let r : Asc82Res11a := ⟨h111N, h112, h113, h114, h115b, h115c, h115d⟩
  have h116 := asc82Lemma116_of h111N
  have h117 := asc82Lemma117_of hp r (asc82Step117R_of hp r)
  have h118 := asc82Lemma118_of hp r h116 h117 (asc82Step118D2_of hp r h116 h117)
  have h119 := asc82Lemma119_of hp r h117 h118
  have h1110 := asc82Lemma1110_of hp r h118 i.type1110 i.single1110
  have h1111 := asc82Lemma1111_of (asc82Step1111X_of hp r h119 h1110 i.dihSd)
    (asc82Step1111K_of hp r h119 h1110 (asc82Step1111KBig_of r i.kBigSD))
  exact ⟨r, h116, h117, h118, h119, h1110, h1111⟩

theorem asc82Lemma1112_of_pre (hp : Asc82Pre11) (hCor : Asc82CorIII) (i : Asc82Inputs11) :
    Asc82Lemma1112 :=
  asc82Lemma1112_of (asc82Step111TR_of hp.r10.l109 (asc82Step111T_of hp))
    (asc82Res11_of_pre hp i).l1111 (asc82StepPocketOfNormal_of hp.basic hp.facts.pockets5) hCor
    hp.r10.l1011

theorem asc82Lemma1210_of_inputs (i : Asc82Omega5Inputs) : Asc82Lemma1210 := by
  have hp := asc82Pre11_of_inputs i
  have h120 := asc82Lemma120_of hp
  have h121 := asc82Lemma121_of hp asc82Prince_of
  have hNoZ4 := asc82StepNoZ4_of_out hp i.split5 i.z4out
  have h122 := asc82Lemma122_of hp h121 i.split5 hNoZ4
  have h123 := asc82Lemma123_of hp h121 i.l63 (asc82Hyp62All_of_aschOmega6Plus i.h6p) i.l65
    hNoZ4
  have h124 := asc82Lemma124_of h121 hNoZ4
  have h125a := asc82Lemma125a_of hp h124
  have h125b := asc82Lemma125b_of hp h122 h123 h124 h125a
  have h126 := asc82Lemma126_of hp h120 h121 h122 h123 h124
  have h127 := asc82Lemma127_of hp h120 h121 h123 h124 h125a h125b h126
    (asc82StepFusionX_of hp h123 hp.facts.invB)
  have h128 := asc82Lemma128_of_K (asc82Lemma128K_of hp h123 h124 h125a h125b h127 i.z2a5
    asc82S8NoL34X_of asc82S8NoL216_of i.s8Dich asc82S8Split_of)
  have h129 := asc82Lemma129_of_J (asc82Lemma129J_of hp h122 h124 h125a h128)
  exact asc82Lemma1210_of hp h126 h129 (asc82Step1210N_of hp h122 h124 h125a h125b h128)

end CFSG.OddStandard.SmallF3.Omega
