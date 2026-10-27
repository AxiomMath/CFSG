module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem normal_subgroupOf_of_commutator_le {V W : Subgroup G} (h : ⁅W, W⁆ ≤ V) :
    (V.subgroupOf W).Normal := by
  refine ⟨fun v hv w => Subgroup.mem_subgroupOf.mpr ?_⟩
  have h1 : ⁅(w : G), (v : G)⁆ ∈ V :=
    h (Subgroup.commutator_mem_commutator w.2 v.2)
  have e : ((w * v * w⁻¹ : ↥W) : G) = ⁅(w : G), (v : G)⁆ * (v : G) := by
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [mul_assoc (((w : G) * (v : G)) * (w : G)⁻¹) ((v : G)⁻¹) (v : G),
      inv_mul_cancel, mul_one]
  rw [e]
  exact V.mul_mem h1 (Subgroup.mem_subgroupOf.mp hv)

theorem isMulCommutative_quotient_subgroupOf_of_commutator_le {V W : Subgroup G}
    (h : ⁅W, W⁆ ≤ V) [(V.subgroupOf W).Normal] :
    IsMulCommutative (↥W ⧸ V.subgroupOf W) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  refine Subgroup.commutator_le.mpr fun a _ b _ => Subgroup.mem_subgroupOf.mpr ?_
  simpa [commutatorElement_def] using
    h (Subgroup.commutator_mem_commutator a.2 b.2)

end CFSG.GroupTheory
