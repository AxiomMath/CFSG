module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsZ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma124_of (h121 : Asc82Lemma121) (hNoZ4 : Asc82StepNoZ4) : Asc82Lemma124 := by
  intro G _ _ t L S z K1 K2 E hctx
  exact (h121 G t L S z K1 K2 E hctx).1.resolve_right (hNoZ4 G t L S z K1 K2 E hctx)

end CFSG.OddStandard.SmallF3.Omega
