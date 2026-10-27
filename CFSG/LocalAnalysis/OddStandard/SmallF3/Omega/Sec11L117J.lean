module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_JMod_eq_of_key [Finite G] {z : G} {T W : Subgroup G} (hWT : W ≤ T) (hzW : z ∈ W)
    (hW : IsElemAbelianMod z W)
    (hkey : ∀ V : Subgroup G, V ≤ T → IsElemAbelianMod z V → V ≤ W ∨ Nat.card V < Nat.card W) :
    JMod z T = W := by
  have hmax : IsMaxElemAbelianMod z T W := by
    refine ⟨hWT, hzW, hW, fun V hVT _ hV => ?_⟩
    rcases hkey V hVT hV with h | h
    · exact Subgroup.card_le_of_le h
    · exact h.le
  apply le_antisymm
  · refine (Subgroup.closure_le W).mpr ?_
    rintro x ⟨U, hU, hx⟩
    rcases hkey U hU.1 hU.2.2.1 with h | h
    · exact h hx
    · exact absurd (hU.2.2.2 W hWT hzW hW) (not_le.mpr h)
  · intro x hx
    exact Subgroup.subset_closure ⟨W, hmax, hx⟩

end CFSG.OddStandard.SmallF3.Omega
