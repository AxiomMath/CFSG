module

public import CFSG.GF2Type.SmithTypeE.E6Order
public import CFSG.LargeExtraspecial.S14SMKLbar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SMK (Inputs10 cMbar cMbar_eq_normalizer_of_noA2
  Lbar_eq_iff_cl_eq_of_noA2)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem not_nonempty_mulEquiv_psl (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) :
    ¬ Nonempty (G ≃* PSL(S.width + 2, ZMod 2)) := by
  rintro ⟨e⟩
  have h2 := factorization_card_of_L6 S hw hU
  have h66 := SmithQ.factorization_card_psl (S.width + 2)
  rw [← Nat.card_congr e.toEquiv, hw] at h66
  omega

theorem not_nonempty_mulEquiv_psu (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) :
    ¬ Nonempty (G ≃* timmesfeldPSU (S.width + 2)) := by
  rintro ⟨e⟩
  have h2 := factorization_card_of_L6 S hw hU
  rw [hw] at e
  have h38 : 2 ^ 38 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv]
    exact SmithQ.two_pow_dvd_card_timmesfeldPSU_twelve
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h38
  omega

theorem irreducible [IsSimpleGroup G] (hDW : DW.DW37Statement) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : ¬ S.IsReducible := fun hred =>
  not_nonempty_mulEquiv_psl hw hU (hDW G S g (by omega) haQ hne hred)

theorem exists_conj_mem_QG [IsSimpleGroup G] (hAS : AschbacherSmithWideInput)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z := by
  by_contra h
  push Not at h
  exact not_nonempty_mulEquiv_psu hw hU (hAS G S (by omega) h)

theorem noA2_of_insp5 [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
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

theorem Lbar_eq_iff_cl_eq [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hbQ : h * S.z * h⁻¹ ∈ S.QG) (hbne : h * S.z * h⁻¹ ≠ S.z) :
    S.Lbar h = S.Lbar g ↔ S.cl (h * S.z * h⁻¹) = S.cl (g * S.z * g⁻¹) :=
  Lbar_eq_iff_cl_eq_of_noA2 (by omega) haQ hne (noA2_of_insp5 I hw hU haQ hne) hbQ hbne

end CFSG.GF2Type.SmithTypeE.L6
