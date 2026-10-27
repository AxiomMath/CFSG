module

public import CFSG.LieType.Steinberg.RankTwo.G2CommData

public section

namespace CFSG.LieType.Steinberg.RankTwo

open CFSG.LieType.Chevalley.RootOps

theorem g2CommCheckRange_0 : g2CommCheckRange 0 2 = true := by
  decide +kernel

theorem g2CommCheckRange_2 : g2CommCheckRange 2 2 = true := by
  decide +kernel

theorem g2CommCheckRange_4 : g2CommCheckRange 4 2 = true := by
  decide +kernel

theorem g2CommCheckRange_6 : g2CommCheckRange 6 2 = true := by
  decide +kernel

theorem g2CommCheckRange_8 : g2CommCheckRange 8 2 = true := by
  decide +kernel

theorem g2CommCheckRange_10 : g2CommCheckRange 10 2 = true := by
  decide +kernel

theorem g2CommCheckRange_12 : g2CommCheckRange 12 2 = true := by
  decide +kernel

theorem g2CommCheckRange_14 : g2CommCheckRange 14 2 = true := by
  decide +kernel

theorem g2CommCheckRange_16 : g2CommCheckRange 16 2 = true := by
  decide +kernel

theorem g2CommCheckRange_18 : g2CommCheckRange 18 2 = true := by
  decide +kernel

theorem g2CommCheckRange_20 : g2CommCheckRange 20 2 = true := by
  decide +kernel

theorem g2CommCheckRange_22 : g2CommCheckRange 22 2 = true := by
  decide +kernel

theorem g2CommCheckRange_24 : g2CommCheckRange 24 2 = true := by
  decide +kernel

theorem g2CommCheckRange_26 : g2CommCheckRange 26 2 = true := by
  decide +kernel

theorem g2CommCheckRange_28 : g2CommCheckRange 28 2 = true := by
  decide +kernel

theorem g2CommPairs_check : g2CommPairs.all (fun e => repCheck .G2 e.1.1 e.1.2 e.2) = true := by
  have hr : ∀ i < 15, g2CommCheckRange (2 * i) 2 = true := by
    intro i hi
    interval_cases i
    exacts [g2CommCheckRange_0, g2CommCheckRange_2, g2CommCheckRange_4, g2CommCheckRange_6,
      g2CommCheckRange_8, g2CommCheckRange_10, g2CommCheckRange_12, g2CommCheckRange_14,
      g2CommCheckRange_16, g2CommCheckRange_18, g2CommCheckRange_20, g2CommCheckRange_22,
      g2CommCheckRange_24, g2CommCheckRange_26, g2CommCheckRange_28]
  refine List.all_eq_true.2 fun e he => ?_
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 he
  have hlt : n < 30 := (List.getElem?_eq_some_iff.1 hn).1
  have := List.all_eq_true.1 (hr (n / 2) (by omega)) n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  simp only [hn] at this
  exact this

theorem g2CommAllOk_eq : g2CommAllOk = true := by
  decide +kernel

end CFSG.LieType.Steinberg.RankTwo
