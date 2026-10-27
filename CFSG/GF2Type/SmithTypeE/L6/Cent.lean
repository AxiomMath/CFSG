module

public import CFSG.GF2Type.SmithTypeE.L6.Defs
public import CFSG.LargeExtraspecial.S14SMELocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem mem_cent2 {t u x : G} : x ∈ cent2 t u ↔ Commute x t ∧ Commute x u := by
  rw [mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem z_mem_cent2 (S : Setting G) {t u : G} (htM : t ∈ S.M) (huM : u ∈ S.M) :
    S.z ∈ cent2 t u :=
  mem_cent2.mpr ⟨(S.mem_M_iff.mp htM).symm, (S.mem_M_iff.mp huM).symm⟩

theorem isConj_mul_z (S : Setting G) {x : G} (hx : IsConj S.z x) (hxQ : x ∈ S.QG)
    (hxz : x ≠ S.z) : IsConj S.z (x * S.z) := by
  refine SME.isConj_of_cl_eq S hx hxQ (S.QG.mul_mem hxQ S.z_mem_QG) ?_ ?_
  · intro h1
    apply hxz
    calc x = x * S.z * S.z := by rw [mul_assoc, S.z_mul_z, mul_one]
      _ = S.z := by rw [h1, one_mul]
  · rw [S.cl_mul hxQ S.z_mem_QG, S.cl_z, add_zero]

end CFSG.GF2Type.SmithTypeE.L6
