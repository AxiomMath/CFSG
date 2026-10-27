module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.M23SylowElem
import CFSG.Assembly.Defs

public section

namespace CFSG.EvenSporadicStandard.Wong77

open CFSG.Blueprint CFSG.EvenSporadicStandard.Wong77.M23Sylow
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem invs16_spec : ∀ k, (invs16 k).length = 15 ∧ (invs16 k).Nodup ∧
    ∀ x ∈ invs16 k, x ≠ 1 ∧ x * x = 1 := by
  intro k
  obtain ⟨hlen, hnd, hall⟩ := of_decide_eq_true (invsOK_elemTabs k)
  refine ⟨?_, List.Nodup.of_map tab (by rwa [tab_invs16]), fun x hx => ?_⟩
  · rw [← List.length_map (f := tab), tab_invs16]
    exact hlen
  · obtain ⟨h1, h2⟩ := hall (tab x) (by rw [← tab_invs16]; exact List.mem_map_of_mem hx)
    refine ⟨fun h => h1 (by rw [h, tab_one]), tab_injective ?_⟩
    rw [tab_mul, h2, tab_one]

end CFSG.EvenSporadicStandard.Wong77
