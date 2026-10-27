module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_s1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_20c
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_21
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_18
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_17
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_16
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Easy

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Lin2

structure Lin2Inputs : Prop where
  tiAbelian : TIAbelianTwoGroupCommute
  singer : SingerNormalizerCyclic
  lemma248 : Lemma2_4_8
  lemma2411 : Lemma2_4_11
  lemma2412 : Lemma2_4_12
  lemma2414 : Lemma2_4_14
  lemma2421 : Lemma2_4_21_core
  lemma2424 : Lemma2_4_24_core
  fusion : Lemma2_4_s1_fusion
  caseS2 : Lemma2_4_s2
  hall : Lin2HallExists

theorem lin2BlockExcluded_of_inputs (h : Lin2Inputs) : Lin2BlockExcluded := by
  intro G _ _ T M H S L hcs n hn hlin
  obtain ⟨D, hhall, hnorm⟩ := h.hall G T M H S L hcs n hn hlin
  by_cases hs : conjJoin S L = L
  · rw [hs] at hhall hnorm
    have hcfg : Lin2Cfg G T M H S L n D := ⟨hcs, hs, hn, hlin, hhall, hnorm⟩
    have h16 := lemma2_4_16 h.lemma248 h.lemma2411 lemma244
    have h17 := lemma2_4_17 h.singer h.lemma248 h.lemma2412 h.lemma2414 h16
    have h18 := lemma2_4_18 h.lemma248 h.lemma2411 h.lemma2414 h16 h17
    have h19 := lemma2_4_19 h.tiAbelian h.lemma248 h.lemma2414 h16 h17 h18
    have h21 := lemma2_4_21 h.lemma248 h16 h19 h.lemma2421
    have h22 := lemma2_4_22 h.lemma248 h.lemma2412 h.lemma2414 h21
    have h24 := lemma2_4_24 h.lemma248 h.lemma2412 h.lemma2414 h17 h22 h.lemma2424
    exact lemma2_4_s1_end h.lemma248 h.lemma2412 h21 h22 h24 h.fusion G T M H S L D n hcfg
  · exact h.caseS2 G T M H S L D n ⟨hcs, hs, hn, hlin, hhall, hnorm⟩

end CFSG.QuasithinUnique
