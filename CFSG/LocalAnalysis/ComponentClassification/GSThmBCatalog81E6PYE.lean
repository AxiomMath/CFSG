module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PYO
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PYM
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PYJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PYC

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem cf81E6P211Spor_of
    (hM12 : P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .M12)
    (hM22 : P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .M22)
    (hM23 : P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .M23)
    (hJ1 : P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .J1)
    (hJ2 : P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .J2)
    (hJ3 : P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .J3)
    (hMcL : P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .McL)
    (hLy : P211For fun G _ => Blueprint.NativeSporadic.IsSporadic G .Ly) :
    CF81E6P211Spor := by
  intro X _ _ hsimp hcent hX
  rcases hX with h | h | h | h | h | h | h | h
  · exact hM12 X hsimp hcent h
  · exact hM22 X hsimp hcent h
  · exact hM23 X hsimp hcent h
  · exact hJ1 X hsimp hcent h
  · exact hJ2 X hsimp hcent h
  · exact hJ3 X hsimp hcent h
  · exact hMcL X hsimp hcent h
  · exact hLy X hsimp hcent h

theorem cf81E6P211Spor :
    CF81E6P211Spor :=
  cf81E6P211Spor_of P211Y.p211For_M12 P211Y.p211For_M22 P211Y.p211For_M23 P211Y.p211For_J1
    P211Y.p211For_J2 P211Y.p211For_J3 P211Y.p211For_McL P211Y.p211For_Ly

end CFSG.ComponentClassification.GSThmB
