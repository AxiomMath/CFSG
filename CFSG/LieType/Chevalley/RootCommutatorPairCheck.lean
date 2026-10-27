module

public import CFSG.LieType.Chevalley.RootCommutatorPairTable

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

theorem closureCheckAll_G2 : closureCheckAll .G2 = true := by decide +kernel

theorem negCheck_G2 : negCheck .G2 = true := by decide +kernel

theorem tableCheck_G2
    : tableCheck .G2 = true := by decide +kernel

theorem sizeCheck_G2 : (List.range (pairTable .G2).length).all (sizeCheck .G2) = true := by
  decide +kernel

theorem closureCheckAll_F4 : closureCheckAll .F4 = true := by decide +kernel

theorem negCheck_F4 : negCheck .F4 = true := by decide +kernel

theorem tableCheck_F4
    : tableCheck .F4 = true := by decide +kernel

theorem sizeCheck_F4 : (List.range (pairTable .F4).length).all (sizeCheck .F4) = true := by
  decide +kernel

theorem closureCheckAll_D4 : closureCheckAll .D4 = true := by decide +kernel

theorem negCheck_D4 : negCheck .D4 = true := by decide +kernel

theorem tableCheck_D4
    : tableCheck .D4 = true := by decide +kernel

theorem sizeCheck_D4 : (List.range (pairTable .D4).length).all (sizeCheck .D4) = true := by
  decide +kernel

theorem closureCheckAll_E6 : closureCheckAll .E6 = true := by decide +kernel

theorem negCheck_E6 : negCheck .E6 = true := by decide +kernel

theorem tableCheck_E6
    : tableCheck .E6 = true := by decide +kernel

theorem sizeCheck_E6 : (List.range (pairTable .E6).length).all (sizeCheck .E6) = true := by
  decide +kernel

end CFSG.LieType.Chevalley.RootOps
