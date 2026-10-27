module

public import CFSG.LieType.SeitzGeneration.HeisLinearGen
public import CFSG.LieType.SeitzGeneration.HeisLinearNormal
public import CFSG.LieType.SeitzGeneration.NonabLinear

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix
open scoped commutatorElement

theorem linearHeisenbergPlanes_of_torusFourierGen
    (hG : ∀ (F : Type) [Field F] [Finite F] (p : ℕ), p.Prime → 5 ≤ p → p ∣ Nat.card F - 1 →
      TorusFourierGen F p) : LinearHeisenbergPlanes := by
  intro F _ _ p hp hp5 hpq E hcomm _ _ hnc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, hxE, hyE, hxy⟩ := hnc
  have hyx : ⁅y, x⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin p) F) := by
    rw [mem_center_iff_toPSL_eq_one, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ hyE _ hxE)
  have hp2 : p ≠ 2 := by omega
  obtain ⟨P, ω, ξ, hω, hξ, hy, hx⟩ :=
    exists_heisenberg_basis_p hp2 (exists_primitiveRoot_of_dvd_card_sub_one hp hpq) hyx hxy
  have hxZ : x ∉ Subgroup.center (SpecialLinearGroup (Fin p) F) := fun h =>
    hxy (Subgroup.mem_center_iff.1 h y).symm
  have hyZ : y ∉ Subgroup.center (SpecialLinearGroup (Fin p) F) := fun h =>
    hxy (Subgroup.mem_center_iff.1 h x)
  exact closure_centralizers_psl_of_heisenberg_p hp hp5 (hG F p hp hp5 hpq) hxE hyE hxZ hyZ hω hξ
    hy hx

end CFSG.LieType.SeitzGeneration
