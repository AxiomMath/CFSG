module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharOmJ
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX11CharOmField

public section

namespace CFSG.ComponentClassification.CatLeafProof.X11Char

theorem cf81X11CharThree : GSThmB.CF81X11CharThree := by
  intro G _ _ N hconf f
  refine ⟨fun h => ?_, fun hM => ?_⟩
  · rcases h with h | h | h
    · exact eq_one_of_conf_lin hconf (Or.inl rfl) h
    · exact eq_one_of_conf_lin hconf (Or.inr rfl) h
    · exact eq_one_of_conf_psp hconf h
  · have hf := eq_one_of_kConf_pomegaMinus hconf.kConf hM
    subst hf
    exact false_of_conf_pomegaMinus_three hconf hM

end CFSG.ComponentClassification.CatLeafProof.X11Char
