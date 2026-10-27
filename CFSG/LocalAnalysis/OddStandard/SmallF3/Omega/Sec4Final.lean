module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Sec3Results : Prop where
  l33 : Asc82Lemma33
  l36 : Asc82Lemma36
  l37 : Asc82Lemma37
  l38 : Asc82Lemma38
  l39 : Asc82Lemma39
  l311 : Asc82Lemma311

end CFSG.OddStandard.SmallF3.Omega
