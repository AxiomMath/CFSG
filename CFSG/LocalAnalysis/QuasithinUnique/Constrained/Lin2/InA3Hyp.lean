module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_16
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_17
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_18
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_19
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_20c
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_21
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3TI
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Singer

public section

namespace CFSG.QuasithinUnique.Lin2

structure Lin2Hyp : Prop where
  h8 : Lemma2_4_8
  h11 : Lemma2_4_11
  h12 : Lemma2_4_12
  h14 : Lemma2_4_14
  h21core : Lemma2_4_21_core

namespace Lin2Hyp

variable (E : Lin2Hyp)

include E

theorem h16 : Lemma2_4_16 := lemma2_4_16 E.h8 E.h11 lemma244

theorem h17 : Lemma2_4_17 := lemma2_4_17 singerNormalizerCyclic E.h8 E.h12 E.h14 E.h16

theorem h18 : Lemma2_4_18 := lemma2_4_18 E.h8 E.h11 E.h14 E.h16 E.h17

theorem h19 : Lemma2_4_19 :=
  lemma2_4_19 tiAbelianTwoGroupCommute E.h8 E.h14 E.h16 E.h17 E.h18

theorem h20 : Lemma2_4_20 := lemma2_4_20 E.h8 E.h11 E.h16 E.h18 E.h19

theorem h21 : Lemma2_4_21 := lemma2_4_21 E.h8 E.h16 E.h19 E.h21core

theorem h22 : Lemma2_4_22 := lemma2_4_22 E.h8 E.h12 E.h14 E.h21

end Lin2Hyp

end CFSG.QuasithinUnique.Lin2
