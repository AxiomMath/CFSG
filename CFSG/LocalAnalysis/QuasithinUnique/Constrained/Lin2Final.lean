module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In248
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InL246
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411A3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2414
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Main

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Lin2

structure Lin2Cited : Prop where
  lemma246Inputs : Lemma246Inputs
  lemma2411 : Lemma2411Cited
  lemma2423exam : Lemma2_4_23_five_examK

theorem lin2Inputs_of_cited
    (c : Lin2Cited) : Lin2Inputs := by
  have h248 : Lemma248Inputs := Lemma248Inputs.of_lemma246Inputs c.lemma246Inputs
  have h8 : Lemma2_4_8 := lemma2_4_8 h248
  have hcore : Lemma2_4_11_core := lemma2_4_11_core_of_listed h248.l246 h8 c.lemma2411.inputs
  have h11 : Lemma2_4_11 := lemma2_4_11 h8 h248.l246 hcore
  have h12 : Lemma2_4_12 :=
    lemma2_4_12_of h8 (lemma2_4_12_two_of h8 (lemma2_4_12_block h8) (lemma2_4_12_Zne1 h8))
  have h14 : Lemma2_4_14 := lemma2_4_14 h8 h11
  have h21 : Lemma2_4_21_core := lemma2_4_21_core_proved h8 h11 h12 h14
  have h5 : Lemma2_4_23_five :=
    lemma2_4_23_five_of_examK ⟨h8, h11, h12, h14, h21⟩ c.lemma2411.a39 c.lemma2423exam
  have hcf := lin2_core_and_fusion h8 h11 h12 h14 h21 h5
  exact ⟨tiAbelianTwoGroupCommute, singerNormalizerCyclic, h8, h11, h12, h14,
    h21, hcf.1, hcf.2,
    lemma2_4_s2_of_inputs ⟨c.lemma246Inputs, c.lemma2411.a39, c.lemma2411.list⟩, lin2HallExists⟩

theorem lin2BlockExcluded_of_cited
    (c : Lin2Cited) : Lin2BlockExcluded :=
  lin2BlockExcluded_of_inputs (lin2Inputs_of_cited c)

end CFSG.QuasithinUnique
