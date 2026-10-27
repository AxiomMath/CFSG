module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11c_JMod_eq [Finite G] {z : G} {R H : Subgroup G} {N : ℕ} (hHR : H ≤ R)
    (hbig : ∀ V : Subgroup G, V ≤ R → z ∈ V → IsElemAbelianMod z V → V ≤ H ∨ Nat.card V < N)
    (hsmall : ∀ V : Subgroup G, V ≤ H → z ∈ V → IsElemAbelianMod z V → Nat.card V ≤ N)
    (hex : ∃ U : Subgroup G, U ≤ H ∧ z ∈ U ∧ IsElemAbelianMod z U ∧ Nat.card U = N)
    (hgen : H ≤ Subgroup.closure {x : G | ∃ U : Subgroup G, U ≤ H ∧ z ∈ U ∧
      IsElemAbelianMod z U ∧ Nat.card U = N ∧ x ∈ U}) :
    JMod z R = H := by
  obtain ⟨U0, hU0H, hzU0, hU0, hU0N⟩ := hex
  have hmax : ∀ U : Subgroup G, U ≤ H → z ∈ U → IsElemAbelianMod z U → Nat.card U = N →
      IsMaxElemAbelianMod z R U := by
    intro U hUH hzU hU hUN
    refine ⟨hUH.trans hHR, hzU, hU, fun V hVR hzV hV => ?_⟩
    rw [hUN]
    rcases hbig V hVR hzV hV with h | h
    · exact hsmall V h hzV hV
    · exact h.le
  apply le_antisymm
  · refine (Subgroup.closure_le H).mpr ?_
    rintro x ⟨U, hU, hx⟩
    rcases hbig U hU.1 hU.2.1 hU.2.2.1 with h | h
    · exact h hx
    · have hle := hU.2.2.2 U0 (hU0H.trans hHR) hzU0 hU0
      rw [hU0N] at hle
      exact absurd hle (not_le.mpr h)
  · refine hgen.trans (Subgroup.closure_mono ?_)
    rintro x ⟨U, hUH, hzU, hU, hUN, hx⟩
    exact ⟨U, hmax U hUH hzU hU hUN, hx⟩

end CFSG.OddStandard.SmallF3.Omega
