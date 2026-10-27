module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4OuterStd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCentModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsFieldW

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem abTab_ne_idTab_of_sigma {w : List (Fin 2 × Bool)}
    {k : ℕ} (hk : k < 64) (hk0 : 0 < k) (h : sigma (cv w) = wordPerm (tg k)) :
    abTab w ≠ idTab 42 := by
  intro he
  have h1 : wordPerm (tg k) = 1 := by rw [← h, sigma_cv]; exact abPerm_eq_one he
  apply coverParts.distinct k hk 0 hk0
  rw [show tg 0 = [] from rfl]
  exact (tabRep_wordTab (tg k)).tab_eq (h1 ▸ TabRep.idTab)

theorem exists_fixed_involution_T0
    {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)}
    {l : Cover →* E} (hQ : IsQSetting q l) {β : E ≃* E} {ρ : Equiv.Perm (Fin 42)}
    (hρ : ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) (hβ : ∀ e, q (β e) = ρ * q e * ρ⁻¹) :
    ∃ u : E, β u = u ∧ u * u = 1 ∧ q u ∈ T0 ∧ q u ≠ 1 := by
  rcases hρ with rfl | rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := fixed_involution_of hQ (beta_cv_of hQ.ker_le hQ.ql hβ
      (abPerm_conj_of tabRep_r₂ r₂_mul_self tabRep_aS coverParts.autF.1)
      (abPerm_conj_of tabRep_r₂ r₂_mul_self tabRep_bS coverParts.autF.2) witF)
      (cv_witSpec (s := (FreeGroup.invRev witF ++ alphaF witF, 0, 0, 2)) (by simp [witSpecs]))
      (cv_witSpec (s := (wpow witF 2, 0, 0, 1)) (by simp [witSpecs]))
      (abTab_ne_idTab_of_sigma (by norm_num) (by norm_num) sigma_witF)
    exact ⟨_, h1, h2, by rw [hQ.q_l, sigma_witF]; exact tg_mem_T0 28 (by norm_num), h3⟩
  · obtain ⟨h1, h2, h3⟩ := fixed_involution_of hQ (beta_cv_of hQ.ker_le hQ.ql hβ
      (abPerm_conj_of tabRep_r₃ r₃_mul_self tabRep_aS coverParts.autG.1)
      (abPerm_conj_of tabRep_r₃ r₃_mul_self tabRep_bS coverParts.autG.2) witG)
      (cv_witSpec (s := (FreeGroup.invRev witG ++ alphaG witG, 0, 0, 0)) (by simp [witSpecs]))
      (cv_witSpec (s := (wpow witG 2, 0, 0, 0)) (by simp [witSpecs]))
      (abTab_ne_idTab_of_sigma (by norm_num) (by norm_num) sigma_witG)
    exact ⟨_, h1, h2, by rw [hQ.q_l, sigma_witG]; exact tg_mem_T0 8 (by norm_num), h3⟩
  · obtain ⟨h1, h2, h3⟩ := fixed_involution_of hQ (beta_cv_of hQ.ker_le hQ.ql hβ
      (abPerm_conj_of tabRep_r₄ r₄_mul_self tabRep_aS coverParts.autU.1)
      (abPerm_conj_of tabRep_r₄ r₄_mul_self tabRep_bS coverParts.autU.2) witU)
      (cv_witSpec (s := (FreeGroup.invRev witU ++ alphaU witU, 0, 0, 0)) (by simp [witSpecs]))
      (cv_witSpec (s := (wpow witU 2, 0, 0, 1)) (by simp [witSpecs]))
      (abTab_ne_idTab_of_sigma (by norm_num) (by norm_num) sigma_witU)
    exact ⟨_, h1, h2, by rw [hQ.q_l, sigma_witU]; exact tg_mem_T0 4 (by norm_num), h3⟩

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem l34OuterWitnessFact :
    L34OuterWitnessFact := by
  intro G _ _ J P b hJ hL hP hbN hbP hbb hbK
  obtain ⟨q, l, ρ, hρ, hQ, hβ, hT⟩ := GrS4.exists_outer_standard hJ hL hbN hbb hbK hP hbP
  obtain ⟨u, hfix, huu, huT, hu1⟩ := GrS4.exists_fixed_involution_T0 hQ hρ hβ
  obtain ⟨w, hwP, hwJ, hwu⟩ := (hT u).1 huT
  have hP2 : IsPGroup 2 P := GrS4.isPGroup_of_isSylowTwoIn hP
  refine ⟨w, hwP, ?_, ?_, ?_⟩
  · have h1 : jq J ⟨w * w, hP.1 (P.mul_mem hwP hwP)⟩ = 1 := by
      rw [show (⟨w * w, hP.1 (P.mul_mem hwP hwP)⟩ : ↥J) = ⟨w, hwJ⟩ * ⟨w, hwJ⟩ from rfl, map_mul,
        hwu, huu]
    exact eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hwP hwP) h1
  · have hbw : b⁻¹ * w * b ∈ P := conj_mem_of_mem_normalizer hbP hwP
    have h2 := betaHat_jq J hbN ⟨w, hwJ⟩
    rw [hwu, hfix] at h2
    have h1 : jq J ⟨b⁻¹ * w * b, hP.1 hbw⟩ = jq J ⟨w, hP.1 hwP⟩ := by
      rw [show (⟨w, hP.1 hwP⟩ : ↥J) = ⟨w, hwJ⟩ from rfl, hwu, h2]
      rfl
    have h3 := eq_of_jq_eq hP.1 hP2 hbw hwP h1
    calc w * b = b * (b⁻¹ * w * b) := by group
      _ = b * w := by rw [h3]
  · intro hwZ
    have h1 := (mem_zStarIn_iff hwJ).mp hwZ
    rw [hwu, ← hQ.ker] at h1
    exact hu1 h1

end CFSG.ComponentClassification.GrSLit
