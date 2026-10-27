module
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G H : Type*} [Group G] [Group H]

namespace IsUniqueMaximalOvergroup

theorem orderIso {X M : Subgroup G} (f : Subgroup G ≃o Subgroup H)
    (h : IsUniqueMaximalOvergroup X M) : IsUniqueMaximalOvergroup (f X) (f M) where
  isCoatom := (f.isCoatom_iff M).2 h.isCoatom
  le := f.le_iff_le.2 h.le
  eq_of_isCoatom N hN hXN :=
    f.symm_apply_eq.1 (h.eq_of_isCoatom ((f.symm.isCoatom_iff N).2 hN) (f.le_symm_apply.2 hXN))

theorem map {X M : Subgroup G} (e : G ≃* H) (h : IsUniqueMaximalOvergroup X M) :
    IsUniqueMaximalOvergroup (X.map (e : G →* H)) (M.map (e : G →* H)) := by
  simpa [MulEquiv.coe_mapSubgroup] using h.orderIso e.mapSubgroup

theorem smul {X M : Subgroup G} (g : G) (h : IsUniqueMaximalOvergroup X M) :
    IsUniqueMaximalOvergroup (MulAut.conj g • X) (MulAut.conj g • M) := by
  rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
  exact h.map (MulAut.conj g)

end IsUniqueMaximalOvergroup

theorem isUniqueMaximalOvergroup_orderIso_iff (f : Subgroup G ≃o Subgroup H) (X M : Subgroup G) :
    IsUniqueMaximalOvergroup (f X) (f M) ↔ IsUniqueMaximalOvergroup X M :=
  ⟨fun h => by simpa using h.orderIso f.symm, fun h => h.orderIso f⟩

theorem isUniqueMaximalOvergroup_map_iff (e : G ≃* H) (X M : Subgroup G) :
    IsUniqueMaximalOvergroup (X.map (e : G →* H)) (M.map (e : G →* H)) ↔
      IsUniqueMaximalOvergroup X M := by
  simpa [MulEquiv.coe_mapSubgroup] using isUniqueMaximalOvergroup_orderIso_iff e.mapSubgroup X M

theorem isUniqueMaximalOvergroup_smul_iff (g : G) (X M : Subgroup G) :
    IsUniqueMaximalOvergroup (MulAut.conj g • X) (MulAut.conj g • M) ↔
      IsUniqueMaximalOvergroup X M := by
  rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
  exact isUniqueMaximalOvergroup_map_iff (MulAut.conj g) X M

theorem isUniqueMaximalOvergroup_conj_inv_smul_iff (g : G) (X M : Subgroup G) :
    IsUniqueMaximalOvergroup (MulAut.conj g⁻¹ • X) (MulAut.conj g⁻¹ • M) ↔
      IsUniqueMaximalOvergroup X M :=
  isUniqueMaximalOvergroup_smul_iff g⁻¹ X M

theorem mem_conj_inv_smul_iff {g x : G} {X : Subgroup G} :
    x ∈ MulAut.conj g⁻¹ • X ↔ g * x * g⁻¹ ∈ X := by
  simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]

end CFSG.FeitThompson
