module

public import CFSG.Certificates.Kernel.CosetW.Sound
public import CFSG.Certificates.CosetTableColumns

public noncomputable section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

theorem subsetCheckC_eq_checkW {m : Nat} (ws : List (List (Fin m × Bool))) (S : List Nat)
    {cap n : Nat} (hcap : (cap + 2) * ((cols ws).length + 1) ≤ 2 ^ 32) :
    subsetCheckC ws S cap n = checkW (mkParamsW (cols ws).length (colInv ws) (colCodes ws ws)
      (colCodes ws ((subsetOf m S).map fun x => [(x, true)]))) cap n := by
  rw [mkParamsW_eq]
  exact (checkW_eq (P := colParams ws ((subsetOf m S).map fun x => [(x, true)])) n hcap).symm

end CFSG.CosetTable
