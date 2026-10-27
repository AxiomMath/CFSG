module

public import CFSG.GF2Type.SmithTypeE.L6.Defs
public import CFSG.LargeExtraspecial.S14SMFOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SME (mem_Qa_iff)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem fixQt_eq_of_smithL6E34a (h34a : SmithL6E34a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {t : G}
    (ht : IsConj S.z t) (htM : t ∈ S.M) (htQ : t ∉ S.QG) :
    S.fixQt t = S.clSub (S.QG ⊓ centralizer ({t} : Set G)) := by
  by_contra hne
  obtain ⟨y, -, hy⟩ := S.lemma_3_2_1 htM hne
  exact h34a G S hw hU t ht htM htQ (ht.trans (isConj_iff.mpr ⟨y, hy⟩))

theorem mem_commQt_of_mem_Qa (h34a : SmithL6E34a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {g v : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) (hvQ : v ∈ S.QG)
    (hv : v ∈ S.Qa g) : S.cl v ∈ S.commQt (g * S.z * g⁻¹) := by
  have hxc : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hno : ¬ ∃ r ∈ S.QG, r * (g * S.z * g⁻¹) * r⁻¹ = g * S.z * g⁻¹ * S.z := by
    rintro ⟨r, -, hr⟩
    exact h34a G S hw hU _ hxc hxM hxQ (hxc.trans (isConj_iff.mpr ⟨r, hr⟩))
  obtain ⟨r, hr, h | h⟩ :=
    SMF.mem_commutator_of_mem_Qa S hxM hxQ hvQ ((mem_Qa_iff S g v).mp hv) hno
  · exact (S.mem_commQt_iff hxM).mpr ⟨r, hr, by rw [h]⟩
  · exact (S.mem_commQt_iff hxM).mpr
      ⟨r, hr, by rw [h, S.cl_mul hvQ S.z_mem_QG, S.cl_z, add_zero]⟩

end CFSG.GF2Type.SmithTypeE.L6
