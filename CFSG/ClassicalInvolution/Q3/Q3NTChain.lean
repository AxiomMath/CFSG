module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameModelPSU
public import CFSG.ClassicalInvolution.Q3.LieSystem
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NT

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem statedLieAdmissible_three {t : StatedLieTag} {n : ℕ} (ht : t = .PSL ∨ t = .PSU)
    (hn : 3 ≤ n) : StatedLieAdmissible t n 3 1 := by
  rcases ht with rfl | rfl
  · refine ⟨Nat.prime_three, le_rfl, by omega, ?_, ?_⟩
    · intro h
      simp at h
    · intro h
      simp at h
      omega
  · refine ⟨Nat.prime_three, le_rfl, hn, ?_⟩
    intro h
    simp at h

section Chain

theorem chainPair_model_three (t : StatedLieTag) (n : ℕ) (ht : t = .PSL ∨ t = .PSU)
    (hn : 3 ≤ n) : Asc77.ChainPair (CompData.model t n).fund :=
  Asc77.chainPair_model (p := 3) (by norm_num) t n 1 ht hn (statedLieAdmissible_three ht hn)

end Chain

end CFSG.ClassicalInvolution.Q3.Q3NT
