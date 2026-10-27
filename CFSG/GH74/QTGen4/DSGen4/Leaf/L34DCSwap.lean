module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34Gamma

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

theorem dcProp_congr {G : Type} [Group G] {A B A' B' : Subgroup G} (h : DCProp A B)
    (hA : A = A') (hB : B = B') : DCProp A' B' := by
  subst hA hB
  exact h

theorem dcStdSwap_of_dcStd {F : Type} [Field F] [Finite F] [CharP F 2] (h : DCStd F) : DCStdSwap F := by
  refine dcProp_of_map (gammaAut F) (Pt F) (Ln F) ?_
  exact dcProp_congr h (gammaAut_map_Pt F).symm (gammaAut_map_Ln F).symm

end CFSG.GH74.QTGen4.DSGen4.L34
