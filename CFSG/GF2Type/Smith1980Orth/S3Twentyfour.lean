module

public import CFSG.GF2Type.Smith1980Orth.S2Seven
public import CFSG.GF2Type.Smith1980Orth.S3Types

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

private theorem betaV_apply_self_of_isTypeA {c : Vt S D.g D.t ≃ₗ[ZMod 2] Vt S D.g D.t}
    (hc : IsTypeA D.QV c 2) (v : Vt S D.g D.t) : D.betaV v (c v) = 0 := by
  have h := hc.2.2.2.2 (c v - v) (sub_mem_commSpace c v)
  rw [map_sub_eq_polar (OrthoF2.mem_orthogonalGroup_of_isTypeA hc), D.polar_QV,
    D.betaV_symm] at h
  exact h

private theorem apply_fst_mem_Pfst {a : S.O} (ha : D.IsTInv a ∨ D.IsUInv a)
    (σ : Vt S D.g D.t) : (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ, 0)) ∈ D.Pfst σ := by
  rcases ha with (rfl | rfl | rfl) | ⟨hs, hA⟩
  · rw [D.t_apply_coord, add_zero]
    exact D.mem_Pfst_iff.mpr ⟨σ, 0, D.betaV_isAlt σ, by rw [zero_smul]⟩
  · rw [coe_mul_apply, D.t_apply_coord, add_zero, D.k_apply_coord, add_zero]
    exact D.mem_Pfst_iff.mpr ⟨0, 1, map_zero _, by rw [one_smul]⟩
  · rw [coe_mul_apply, coe_mul_apply, D.t_apply_coord, add_zero, D.k_apply_coord, add_zero,
      D.k_apply_coord, zero_add]
    exact D.mem_Pfst_iff.mpr ⟨σ, 1, D.betaV_isAlt σ, by rw [one_smul]⟩
  · refine D.mem_Pfst_iff.mpr ⟨D.resC ⟨a, hs⟩ σ, 0,
      D.betaV_apply_self_of_isTypeA hA σ, ?_⟩
    rw [zero_smul]
    exact (D.Cbar_apply_coord ⟨a, hs⟩ σ 0).trans (by rw [map_zero])

private theorem apply_snd_mem_Psnd {a : S.O} (ha : D.IsTInv a ∨ D.IsUInv a)
    (σ : Vt S D.g D.t) : (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (0, σ)) ∈ D.Psnd σ := by
  rcases ha with (rfl | rfl | rfl) | ⟨hs, hA⟩
  · rw [D.t_apply_coord]
    exact D.mem_Psnd_iff.mpr ⟨0, 1, map_zero _, by rw [one_smul, zero_add]⟩
  · rw [coe_mul_apply, D.t_apply_coord, D.k_apply_coord]
    exact D.mem_Psnd_iff.mpr ⟨σ, 1, D.betaV_isAlt σ, by rw [one_smul, zero_add]⟩
  · rw [coe_mul_apply, coe_mul_apply, D.t_apply_coord, D.k_apply_coord, D.k_apply_coord]
    refine D.mem_Psnd_iff.mpr ⟨σ, 0, D.betaV_isAlt σ, ?_⟩
    rw [zero_smul, zero_add, OrthoF2.vec_add_self, add_zero]
  · refine D.mem_Psnd_iff.mpr ⟨D.resC ⟨a, hs⟩ σ, 0,
      D.betaV_apply_self_of_isTypeA hA σ, ?_⟩
    rw [zero_smul, add_zero]
    exact (D.Cbar_apply_coord ⟨a, hs⟩ 0 σ).trans (by rw [map_zero])

private theorem apply_diag_mem_Pdiag {a : S.O} (ha : D.IsTInv a ∨ D.IsUInv a)
    (σ : Vt S D.g D.t) : (a : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.coord (σ, σ)) ∈ D.Pdiag σ := by
  rcases ha with (rfl | rfl | rfl) | ⟨hs, hA⟩
  · rw [D.t_apply_coord]
    exact D.mem_Pdiag_iff.mpr ⟨σ, 1, D.betaV_isAlt σ, by rw [one_smul]⟩
  · rw [coe_mul_apply, D.t_apply_coord, D.k_apply_coord]
    refine D.mem_Pdiag_iff.mpr ⟨σ, 0, D.betaV_isAlt σ, ?_⟩
    rw [zero_smul, add_zero, OrthoF2.vec_add_self, zero_add]
  · rw [coe_mul_apply, coe_mul_apply, D.t_apply_coord, D.k_apply_coord, D.k_apply_coord]
    refine D.mem_Pdiag_iff.mpr ⟨0, 1, map_zero _, ?_⟩
    rw [one_smul, OrthoF2.vec_add_self, zero_add, OrthoF2.vec_add_self]
  · refine D.mem_Pdiag_iff.mpr ⟨D.resC ⟨a, hs⟩ σ, 0,
      D.betaV_apply_self_of_isTypeA hA σ, ?_⟩
    rw [zero_smul, add_zero]
    exact D.Cbar_apply_coord ⟨a, hs⟩ σ σ

theorem oe24_of_types (h : D.OTypes) : OE24 S := by
  intro x g hx hxM hxQ hgQ
  by_cases hgz : g * S.z * g⁻¹ = S.z
  · rw [hgz, S.Qa_eq_QG_of_conj_eq hgz, S.z_comm hxM, mul_inv_cancel_right]
    exact S.z_mem_QG
  have hgc : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨σ, -, -, hcl⟩ := (D.isConj_z_iff_coord hgQ hgz).mp hgc
  have ha := h x hx hxM hxQ
  have hxy : x * (g * S.z * g⁻¹) * x⁻¹ ∈ S.QG := S.conj_mem_QG hxM hgQ
  have hclx : S.cl (x * (g * S.z * g⁻¹) * x⁻¹) =
      (S.ρ ⟨x, hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) :=
    (S.ρ_cl ⟨x, hxM⟩ hgQ).symm
  have hz : S.z ∈ S.QG ⊓ S.Qa g := ⟨S.z_mem_QG, S.z_mem_Qa hgQ hgz⟩
  have hmem : S.cl (x * (g * S.z * g⁻¹) * x⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) := by
    rw [hclx]
    rcases hcl with hcl | hcl | hcl
    · rw [hcl, D.clSub_QG_inf_Qa_eq_Pfst hgQ hgz hcl]
      exact D.apply_fst_mem_Pfst ha σ
    · rw [hcl, D.clSub_QG_inf_Qa_eq_Psnd hgQ hgz hcl]
      exact D.apply_snd_mem_Psnd ha σ
    · rw [hcl, D.clSub_QG_inf_Qa_eq_Pdiag hgQ hgz hcl]
      exact D.apply_diag_mem_Pdiag ha σ
  exact ((S.clPre_clSub inf_le_left hz).le ⟨hxy, hmem⟩).2

end S2Data

end CFSG.GF2Type.Smith1980Orth
