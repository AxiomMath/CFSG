module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped Pointwise

variable {n : ℕ}

theorem pointListOK_spec {l : List ℕ} (h : pointListOK n l = true) : PointList n l := by
  simp only [pointListOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, strictIncr_pairwise h.2⟩

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
