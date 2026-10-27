module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowX
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowY
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowZ
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowU
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7SylowV

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

variable {K : Type} [Field K]

section Certs


theorem e7_hJ [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    ∀ y ∈ e7Reps K, ∃ Z u, Exc.CentreData y Z ∧ Exc.Regular Z u ∧ Exc.SylowData y Z := by
  intro y hy
  simp only [e7Reps, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨u, hu⟩ := regular_e7FrameX (K := K)
    exact ⟨_, u, centreData_e7FrameX, hu, sylowData_e7FrameX⟩
  · obtain ⟨u, hu⟩ := regular_e7FrameY (K := K)
    exact ⟨_, u, centreData_e7FrameY h4, hu, sylowData_e7FrameY h4⟩
  · obtain ⟨u, hu⟩ := regular_e7FrameZ (K := K)
    exact ⟨_, u, centreData_e7FrameZ h4, hu, sylowData_e7FrameZ h4⟩
  · obtain ⟨u, hu⟩ := regular_e7FrameU (K := K)
    exact ⟨_, u, centreData_e7FrameU h4, hu, sylowData_e7FrameU h4⟩
  · obtain ⟨u, hu⟩ := regular_e7FrameV (K := K)
    exact ⟨_, u, centreData_e7FrameV h4, hu, sylowData_e7FrameV h4⟩

end Certs

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
