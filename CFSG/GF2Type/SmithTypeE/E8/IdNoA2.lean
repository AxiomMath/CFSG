module

public import CFSG.GF2Type.SmithTypeE.E7Order
public import CFSG.LargeExtraspecial.S14SMKLbar
public import CFSG.LargeExtraspecial.FS77PSU

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SMK (Inputs10 cMbar cMbar_eq_normalizer_of_noA2
  Lbar_eq_iff_cl_eq_of_noA2)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem not_nonempty_mulEquiv_psl (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1) :
    ¬ Nonempty (G ≃* PSL(S.width + 2, ZMod 2)) := by
  rintro ⟨e⟩
  have h2 := factorization_card_of_E8 S hw hU
  have h435 := SmithQ.factorization_card_psl (S.width + 2)
  rw [← Nat.card_congr e.toEquiv, hw] at h435
  omega

theorem not_nonempty_mulEquiv_psu (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1) :
    ¬ Nonempty (G ≃* timmesfeldPSU (S.width + 2)) := by
  rintro ⟨e⟩
  have h2 := factorization_card_of_E8 S hw hU
  have h435 := FS77.factorization_card_timmesfeldPSU (m := S.width + 2) (by omega)
  rw [← Nat.card_congr e.toEquiv, hw] at h435
  omega

theorem irreducible [IsSimpleGroup G] (hDW : DW.DW37Statement) (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : ¬ S.IsReducible := fun hred =>
  not_nonempty_mulEquiv_psl hw hU (hDW G S g (by omega) haQ hne hred)

theorem exists_conj_mem_QG [IsSimpleGroup G] (hAS : AschbacherSmithWideInput)
    (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1) :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z := by
  by_contra h
  push Not at h
  exact not_nonempty_mulEquiv_psu hw hU (hAS G S (by omega) h)

theorem noA2_of_insp5 [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : ¬ S.HasTypeAInL g := by
  rintro ⟨α, hαL, -, hαA⟩
  have ht : S.ρ α ∈ S.Lbar g := by
    rw [← S.map_La_eq_Lbar g]
    exact ⟨α, mem_subgroupOf.mpr hαL, rfl⟩
  rcases Setting.timmesfeld_12_16_of_insp5 I.hRI I.hARS I.hTri I.hFischer I.hInsp I.h36 I.hSL
    haQ hne (by omega) ht hαA with hred | ⟨h4, -⟩ | hR | ⟨h4, -⟩
  · exact irreducible I.hDW hw hU haQ hne hred
  · omega
  · exact Setting.not_s12GammaLResidual haQ hne (by omega) hR
  · omega

theorem cMbar_eq_normalizer [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    cMbar S g = S.Mbar ⊓ normalizer (S.Lbar g : Set S.O) :=
  cMbar_eq_normalizer_of_noA2 (by omega) haQ hne (noA2_of_insp5 I hw hU haQ hne)

end CFSG.GF2Type.SmithTypeE.E8
