module

public import CFSG.ClassicalInvolution.Q3.TL3T45

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open Certificates.AE117

theorem adjInv_of_ne_eight {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≠ 8) :
    AdjInv n := by
  by_cases hn9 : 9 ≤ n
  · exact AE.adjInv_of_nine_le hn9
  · obtain ⟨⟨hA₅, hA₆, hA₇⟩, -⟩ := ae117_check
    have hn7 : n ≤ 7 := by omega
    interval_cases n
    · exact adjInv_of_check hA₅
    · exact adjInv_of_check hA₆
    · exact adjInv_of_check hA₇

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117
