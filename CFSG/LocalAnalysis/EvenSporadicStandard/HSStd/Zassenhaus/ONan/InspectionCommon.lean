module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.PGL29Facts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.QuasithinUnique

theorem exists_simple_le_of_pgl29 {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hidx : N.index < 360)
    (hw : ∃ w : Y, orderOf w = 2 ∧ ∃ H : Subgroup Y, H ≤ centralizer ({w} : Set Y) ∧
      Nonempty (↥H ≃* ↥A6Models.pgl29)) :
    ∃ w : Y, orderOf w = 2 ∧ ∃ H A : Subgroup Y, H ≤ centralizer ({w} : Set Y) ∧ w ∉ H ∧
      (∃ h ∈ H, orderOf h = 8) ∧ (∃ d ∈ H, orderOf d = 10) ∧ A ≤ H ∧ A ≤ N ∧
      Nat.card A = 360 ∧ IsSimpleGroup ↥A ∧ ⁅A, A⁆ = A ∧ ∀ x ∈ H, x ^ 2 ∈ A := by
  obtain ⟨w, hw2, H, hH, ⟨e⟩⟩ := hw
  obtain ⟨hwH, h8, d10, A, hAH, hA, hsimple, hperf, hsq⟩ := pgl29_copy_facts e hw2 hH
  have hAN : A ≤ N := le_of_isSimpleGroup_of_index_lt (by rw [hA]; exact hidx)
  exact ⟨w, hw2, H, A, hH, hwH, h8, d10, hAH, hAN, hA, hsimple, hperf, hsq⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
