module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FXQBCentSq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FStdChar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem fx_qb_sq_mem_centralizer_of_om6z2 (hL : IsOm6Z2 L) {B : Subgroup G} (hBL : B ≤ L)
    (hB : IsElemAb2 B 5) (hBZ : Nat.card ↥(B ⊓ centerIn L) ≤ 2) {y : G}
    (hyN : y ∈ normalizer (L : Set G)) (hyB : y ∈ centralizer (B : Set G)) :
    y * y ∈ centralizer (L : Set G) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hsgn, ⟨e⟩⟩ :=
    isOmegaStar_of_lieModel_psu (s7f_lieModel_center_of_twoU43 hL.1 hL.2)
  exact fx_qb_sq_mem_centralizer hBL hB hBZ hdim hsgn e
    (Group.isPerfect_def.mp hL.1.1) hyN hyB

end CFSG.OddStandard.SmallF3.Omega
