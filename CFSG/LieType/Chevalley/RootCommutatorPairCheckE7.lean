module

public import CFSG.LieType.Chevalley.RootCommutatorPairTable

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem closureCheck_E7_0 : closureCheck .E7 ⟨0, by decide⟩ 0 126 = true := by
  decide +kernel

theorem closureCheck_E7_1 : closureCheck .E7 ⟨1, by decide⟩ 0 126 = true := by
  decide +kernel

theorem closureCheck_E7_2 : closureCheck .E7 ⟨2, by decide⟩ 0 126 = true := by
  decide +kernel

theorem closureCheck_E7_3 : closureCheck .E7 ⟨3, by decide⟩ 0 126 = true := by
  decide +kernel

theorem closureCheck_E7_4 : closureCheck .E7 ⟨4, by decide⟩ 0 126 = true := by
  decide +kernel

theorem closureCheck_E7_5 : closureCheck .E7 ⟨5, by decide⟩ 0 126 = true := by
  decide +kernel

theorem closureCheck_E7_6 : closureCheck .E7 ⟨6, by decide⟩ 0 126 = true := by
  decide +kernel

theorem negCheck_E7 : negCheck .E7 = true := by decide +kernel

theorem tableCheck_E7
    : tableCheck .E7 = true := by decide +kernel

theorem sizeCheck_E7 : (List.range (pairTable .E7).length).all (sizeCheck .E7) = true := by
  decide +kernel

theorem closureOK_E7 : ClosureOK .E7 := by
  intro i m n hm hn
  fin_cases i
  · exact closureCheck_spec closureCheck_E7_0 (Nat.zero_le m) hm hn
  · exact closureCheck_spec closureCheck_E7_1 (Nat.zero_le m) hm hn
  · exact closureCheck_spec closureCheck_E7_2 (Nat.zero_le m) hm hn
  · exact closureCheck_spec closureCheck_E7_3 (Nat.zero_le m) hm hn
  · exact closureCheck_spec closureCheck_E7_4 (Nat.zero_le m) hm hn
  · exact closureCheck_spec closureCheck_E7_5 (Nat.zero_le m) hm hn
  · exact closureCheck_spec closureCheck_E7_6 (Nat.zero_le m) hm hn

end CFSG.LieType.Chevalley.RootOps
