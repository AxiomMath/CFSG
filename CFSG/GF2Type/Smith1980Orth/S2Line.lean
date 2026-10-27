module

public import CFSG.GF2Type.Smith1980Orth.S2Seven
public import CFSG.GF2Type.Smith1980Orth.PathGlue

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

private theorem exists_conj_of_cl {h : G} (hQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) {v : S.Qt} (hvP : v ∈ S.clSub (S.QG ⊓ S.Qa h)) (hv0 : v ≠ 0)
    (hvb : v ≠ S.cl (h * S.z * h⁻¹))
    (hvc : ∃ s : Vt S D.g D.t, s ≠ 0 ∧ D.QV s = 0 ∧
      (v = D.coord (s, 0) ∨ v = D.coord (0, s) ∨ v = D.coord (s, s))) :
    ∃ c : G, IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ S.Qa h ∧ c ≠ S.z ∧ c ≠ h * S.z * h⁻¹ ∧
      c ≠ S.z * (h * S.z * h⁻¹) := by
  obtain ⟨c, hcQ, hcv⟩ := S.exists_cl v
  have hcz : c ≠ S.z := fun hcz => hv0 (by rw [← hcv, hcz, S.cl_z])
  have hzX : S.z ∈ S.QG ⊓ S.Qa h := ⟨S.z_mem_QG, S.z_mem_Qa hQ hne⟩
  refine ⟨c, ?_, hcQ, ?_, hcz, ?_, ?_⟩
  · exact (D.isConj_z_iff_coord hcQ hcz).mpr (by rwa [hcv])
  · have hc : c ∈ S.clPre (S.clSub (S.QG ⊓ S.Qa h)) := ⟨hcQ, by rw [hcv]; exact hvP⟩
    rw [S.clPre_clSub inf_le_left hzX] at hc
    exact hc.2
  · exact fun hcb => hvb (by rw [← hcv, hcb])
  · intro hcb
    apply hvb
    rw [← hcv, hcb, S.cl_mul S.z_mem_QG hQ, S.cl_z, zero_add]

include D in
theorem oe24Line : OE24Line S := by
  intro h hQ hne
  have hbc : IsConj S.z (h * S.z * h⁻¹) := isConj_iff.mpr ⟨h, rfl⟩
  obtain ⟨σ, hσ0, hσQ, hcl⟩ := (D.isConj_z_iff_coord hQ hne).mp hbc
  rcases hcl with hcl | hcl | hcl
  · refine D.exists_conj_of_cl hQ hne (v := D.coord (0, σ)) ?_ ?_ ?_
      ⟨σ, hσ0, hσQ, Or.inr (Or.inl rfl)⟩
    · rw [D.clSub_QG_inf_Qa_eq_Pfst hQ hne hcl]
      exact D.mem_Pfst_iff.mpr ⟨0, 1, map_zero _, by rw [one_smul]⟩
    · exact fun h0 => hσ0 (congrArg Prod.snd (D.coord.injective (h0.trans (map_zero _).symm)))
    · rw [hcl]
      exact fun he => hσ0 (congrArg Prod.fst (D.coord.injective he)).symm
  · refine D.exists_conj_of_cl hQ hne (v := D.coord (σ, σ)) ?_ ?_ ?_
      ⟨σ, hσ0, hσQ, Or.inr (Or.inr rfl)⟩
    · rw [D.clSub_QG_inf_Qa_eq_Psnd hQ hne hcl]
      exact D.mem_Psnd_iff.mpr ⟨0, 1, map_zero _, by rw [one_smul, zero_add]⟩
    · exact fun h0 => hσ0 (congrArg Prod.fst (D.coord.injective (h0.trans (map_zero _).symm)))
    · rw [hcl]
      exact fun he => hσ0 (congrArg Prod.fst (D.coord.injective he))
  · refine D.exists_conj_of_cl hQ hne (v := D.coord (σ, 0)) ?_ ?_ ?_
      ⟨σ, hσ0, hσQ, Or.inl rfl⟩
    · rw [D.clSub_QG_inf_Qa_eq_Pdiag hQ hne hcl]
      exact D.mem_Pdiag_iff.mpr ⟨0, 1, map_zero _, by rw [one_smul, zero_add]⟩
    · exact fun h0 => hσ0 (congrArg Prod.fst (D.coord.injective (h0.trans (map_zero _).symm)))
    · rw [hcl]
      exact fun he => hσ0 (congrArg Prod.snd (D.coord.injective he)).symm

end S2Data

end CFSG.GF2Type.Smith1980Orth
