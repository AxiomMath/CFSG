module

public import CFSG.CGT.Stroth77.Stroth31Proof

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G]

theorem stroth_3_1'_of_no_index_four (X : StrothAmbient G) {m : ℕ} (Z : StrothDatum X)
    (hτ : Z.τ = StrothTypeIndex.t100 m) (C : Subgroup G) (hDC : Z.D ≤ C)
    (hCR : C ≤ strothR X Z.D) (hmin : IsMinimalLModuleMod Z.dataD C)
    (hno4 : (Z.D.subgroupOf C).index ≠ 4) :
    Nat.card C = 2 * Nat.card Z.D :=
  stroth_3_1 X Z hτ C hDC hCR hmin
    (index_le_four_of_minimal X Z hτ C hDC hCR hmin) hno4

end CFSG.CGT.Stroth77
