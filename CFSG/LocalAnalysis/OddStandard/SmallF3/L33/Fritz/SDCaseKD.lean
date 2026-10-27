module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDAutFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDData

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDCaseKD

open CFSG Subgroup Equiv CFSG.ComponentClassification.HSFLit
open CFSG.ComponentClassification.HSDihedral

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

private theorem field_involution_aux :
    ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8,
      aff8 u b * x8 = x8 * aff8 u b → aff8 u b * y8 = y8 * aff8 u b →
      aff8 u b ∉ R8 → aff8 u b = k8 ∨ aff8 u b = z8 * k8 := by
  decide

private theorem z8_mul_self : z8 * z8 = (1 : Perm (ZMod 8)) := by decide

private theorem z8_pow_two : z8 ^ 2 = (1 : Perm (ZMod 8)) := by
  rw [pow_two, z8_mul_self]

private theorem aff8_u3_one_mul_k8 : aff8 u3 1 * k8 = d8 := by decide

private theorem aff8_u3_one_mem_S16 : aff8 u3 1 ∈ SD.S16 := ⟨u3, 1, rfl, by decide⟩

private theorem commute_of_ψ_eq_z8 (A : SDData t L) {z w : X} (hzT : z ∈ A.T) (hwT : w ∈ A.T)
    (hzL : z ∈ L) (hzψ : A.ψ ⟨z, hzT⟩ = z8) : z * w = w * z := by
  have hcommT : z * w * z⁻¹ * w⁻¹ ∈ A.T := by
    have h1 : z * w ∈ A.T := A.T.mul_mem hzT hwT
    have h2 : z⁻¹ * w⁻¹ ∈ A.T := A.T.mul_mem (A.T.inv_mem hzT) (A.T.inv_mem hwT)
    have h3 : (z * w) * (z⁻¹ * w⁻¹) ∈ A.T := A.T.mul_mem h1 h2
    simpa only [mul_assoc] using h3
  have hK : z * w * z⁻¹ * w⁻¹ ∈ A.K := by
    rw [A.mem_K_iff hcommT]
    have hzw : A.ψ ⟨z, hzT⟩ * A.ψ ⟨w, hwT⟩ = A.ψ ⟨w, hwT⟩ * A.ψ ⟨z, hzT⟩ := by
      rw [hzψ]
      obtain ⟨u, b, hub⟩ := A.ψ_mem_H8 ⟨w, hwT⟩
      rw [← hub]
      exact (SD.z8_comm_aff8' u b).symm
    rw [show (⟨z * w * z⁻¹ * w⁻¹, hcommT⟩ : ↥A.T) =
        (⟨z, hzT⟩ : ↥A.T) * ⟨w, hwT⟩ * (⟨z, hzT⟩ : ↥A.T)⁻¹ * (⟨w, hwT⟩ : ↥A.T)⁻¹ from rfl]
    simp only [map_mul, map_inv]
    rw [hzw]
    group
  have hwN : w ∈ normalizer (L : Set X) := A.config.le_normalizer (A.T_le_centralizer hwT)
  have hL : z * w * z⁻¹ * w⁻¹ ∈ L := by
    have hconj : w * z⁻¹ * w⁻¹ ∈ L := (mem_normalizer_iff.mp hwN z⁻¹).mp (L.inv_mem hzL)
    simpa only [mul_assoc] using L.mul_mem hzL hconj
  have hbot : z * w * z⁻¹ * w⁻¹ = 1 := by
    have h : z * w * z⁻¹ * w⁻¹ ∈ A.K ⊓ L := ⟨hK, hL⟩
    rwa [A.K_inf_L, mem_bot] at h
  have h2 : z * w * z⁻¹ = w := mul_inv_eq_one.mp hbot
  calc z * w = z * w * z⁻¹ * z := by group
    _ = w * z := by rw [h2]

theorem exists_field_involution
    (hH : HaradaInput) (hX : ¬ SectRank4 X) (A : SDData t L) :
    A.K = zpowers t ∧ ∃ (w : X) (hw : w ∈ A.T), w ^ 2 = 1 ∧
      (A.ψ ⟨w, hw⟩ = k8 ∨ A.ψ ⟨w, hw⟩ = z8 * k8) := by
  obtain ⟨hQ, w, hwS, hw2, hwD, hwn⟩ :=
    (SDAutFacts.datum A).coreOut hH (SDAutFacts.autFacts_datum A) hX
  refine ⟨(SDAutFacts.map_ker A).symm.trans hQ, w, hwS, hw2, ?_⟩
  have hα : (SDAutFacts.datum A).ψe w = A.ψ ⟨w, hwS⟩ :=
    (SDAutFacts.datum A).ψe_of_mem hwS
  rw [SDAutFacts.Dbar_datum, hα] at hwD hwn
  obtain ⟨u, b, hub⟩ := A.ψ_mem_H8 ⟨w, hwS⟩
  rw [← hub] at hwn hwD ⊢
  exact field_involution_aux u b (hwD x8 SD.x8_mem_R8) (hwD y8 SD.y8_mem_R8) hwn

theorem caseKD_of_field (A : SDData t L) (hK : A.K = zpowers t) {w : X} (hw : w ∈ A.T)
    (hw2 : w ^ 2 = 1) (hψ : A.ψ ⟨w, hw⟩ = k8 ∨ A.ψ ⟨w, hw⟩ = z8 * k8) :
    Nonempty A.CaseKD := by
  have hcard : Nat.card A.K = 2 := by rw [hK, Nat.card_zpowers, A.orderOf_t]
  obtain ⟨g, hgL, hgψ⟩ := A.exists_ψ_eq (aff8 u3 1) aff8_u3_one_mem_S16
  rcases hψ with hψ | hψ
  · refine ⟨⟨w, hw, hw2, hψ, g.1 * w, mul_mem g.2 hw, ?_, hcard⟩⟩
    rw [show (⟨g.1 * w, mul_mem g.2 hw⟩ : ↥A.T) = g * ⟨w, hw⟩ from rfl, map_mul, hgψ,
      hψ, aff8_u3_one_mul_k8]
  · obtain ⟨z, hz, hzψ⟩ := A.exists_mem_R_ψ_eq SD.z8_mem_R8
    have hzL : z ∈ L := A.R_le_L hz
    have hcomm : z * w = w * z := commute_of_ψ_eq_z8 A hz.1 hw hzL hzψ
    have hz2 : z ^ 2 = 1 := by
      have hT : z ^ 2 ∈ A.T := pow_mem hz.1 2
      have hL : z ^ 2 ∈ L := pow_mem hzL 2
      have hKmem : z ^ 2 ∈ A.K := by
        rw [A.mem_K_iff hT]
        rw [show (⟨z ^ 2, hT⟩ : ↥A.T) = (⟨z, hz.1⟩ : ↥A.T) ^ 2 from rfl, map_pow, hzψ,
          z8_pow_two]
      have hinf : z ^ 2 ∈ A.K ⊓ L := ⟨hKmem, hL⟩
      rwa [A.K_inf_L, mem_bot] at hinf
    refine ⟨⟨z * w, mul_mem hz.1 hw, ?_, ?_, g.1 * (z * w),
      mul_mem g.2 (mul_mem hz.1 hw), ?_, hcard⟩⟩
    · calc (z * w) ^ 2 = z * (w * z) * w := by rw [pow_two]; group
        _ = z * (z * w) * w := by rw [hcomm]
        _ = z ^ 2 * w ^ 2 := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hz2, hw2, one_mul]
    · rw [show (⟨z * w, mul_mem hz.1 hw⟩ : ↥A.T) = (⟨z, hz.1⟩ : ↥A.T) * ⟨w, hw⟩ from rfl,
        map_mul, hzψ, hψ, ← mul_assoc, z8_mul_self, one_mul]
    · rw [show (⟨g.1 * (z * w), mul_mem g.2 (mul_mem hz.1 hw)⟩ : ↥A.T) =
          g * ((⟨z, hz.1⟩ : ↥A.T) * ⟨w, hw⟩) from rfl, map_mul, map_mul, hgψ, hzψ, hψ]
      rw [show z8 * (z8 * k8) = k8 by rw [← mul_assoc, z8_mul_self, one_mul]]
      exact aff8_u3_one_mul_k8

theorem exists_caseKD
    (hH : HaradaInput) (hX : ¬ SectRank4 X) (A : SDData t L) : Nonempty A.CaseKD := by
  obtain ⟨hK, w, hw, hw2, hψ⟩ := exists_field_involution hH hX A
  exact caseKD_of_field A hK hw hw2 hψ

end CFSG.OddStandard.SmallF3.L33.KD.SDCaseKD
