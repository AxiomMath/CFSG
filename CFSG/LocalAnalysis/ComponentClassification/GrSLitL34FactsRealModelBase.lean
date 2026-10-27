
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import Certificates.Data.GrSLitL34FactsRealCheck

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem entryOK_spec {e : ℕ × ℕ × ℕ × ℕ} (h : entryOK e = true) :
    e.1 < 64 ∧ e.2.1 < 4 ∧ e.2.2.1 < 4 ∧ e.2.2.2 < 3 := by
  simpa [entryOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

end CFSG.ComponentClassification.GrSLit.L34Facts.Real
