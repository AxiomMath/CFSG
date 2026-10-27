module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPCls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OP4Rho

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X]

theorem sec5op4_twoCore_le_kerG
    {z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (hπ : Function.Surjective π)
    (hA : Sec5GCaseI (sec5op_Tb z T π) ∨ Sec5GCaseII (sec5op_Tb z T π))
    {K : Subgroup G} (hKH : K ≤ centralizer ({z} : Set G))
    (hKT : ∀ k ∈ K, ∀ a ∈ T, k * a * k⁻¹ = a) (hK : twoRes K = K) :
    twoCoreIn K ≤ sec5op_kerG z T π := by
  intro q hq
  have hqK : q ∈ K := by
    unfold twoCoreIn CFSG.inSubgroup at hq
    exact Subgroup.map_subtype_le _ hq
  have hqH : q ∈ centralizer ({z} : Set G) := hKH hqK
  exact (sec5op_mem_kerG_iff (z := z) (T := T) (π := π)).2
    ⟨hqH, sec5op4_rho_twoCore hπ hA hKH hKT hK hq hqH⟩

end CFSG.OddStandard.SmallF3.Omega
