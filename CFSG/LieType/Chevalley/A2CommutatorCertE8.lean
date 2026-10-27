module

public import CFSG.LieType.Chevalley.A2CommutatorCheck

public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e8_a2CheckRow_0 : a2CheckRow .E8 ⟨0, by decide⟩ = true := by decide +kernel

theorem e8_a2CheckRow_1 : a2CheckRow .E8 ⟨1, by decide⟩ = true := by decide +kernel

theorem e8_a2CheckRow_2 : a2CheckRow .E8 ⟨2, by decide⟩ = true := by decide +kernel

theorem e8_a2CheckRow_3 : a2CheckRow .E8 ⟨3, by decide⟩ = true := by decide +kernel

theorem e8_a2CheckRow_4 : a2CheckRow .E8 ⟨4, by decide⟩ = true := by decide +kernel

theorem e8_a2CheckRow_5 : a2CheckRow .E8 ⟨5, by decide⟩ = true := by decide +kernel

theorem e8_a2CheckRow_6 : a2CheckRow .E8 ⟨6, by decide⟩ = true := by decide +kernel

theorem e8_a2CheckRow_7 : a2CheckRow .E8 ⟨7, by decide⟩ = true := by decide +kernel

theorem a2CheckAll_E8 : a2CheckAll .E8 = true :=
  a2CheckAll_of_rows fun i => by
    fin_cases i
    exacts [e8_a2CheckRow_0, e8_a2CheckRow_1, e8_a2CheckRow_2, e8_a2CheckRow_3,
      e8_a2CheckRow_4, e8_a2CheckRow_5, e8_a2CheckRow_6, e8_a2CheckRow_7]

end CFSG.LieType.Chevalley.RootOps
