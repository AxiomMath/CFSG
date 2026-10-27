module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCentModel
public import Certificates.Certificate22212

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

structure LiftParts : Prop where
  specs : ∀ s ∈ liftSpecs, cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  norm : liftNormOK = true

theorem liftParts : LiftParts :=
  ⟨Certificates.certificate22212.1, Certificates.certificate22212.2⟩

theorem cv_spec_lift
    {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ} (hs : s ∈ liftSpecs) :
    cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2) :=
  liftParts.specs s hs

theorem cv_alpha_liftW0 :
    cv (alphaF liftW0) = cv liftW0 * z₃ ^ 2 ∧ cv (alphaG liftW0) = cv liftW0 * z₃ ^ 2 ∧
      cv (alphaU liftW0) = cv liftW0 ∧ cv liftW0 * cv liftW0 = z₃ := by
  have h := fun s hs => cv_spec_lift (s := s) hs
  have hF := h _ (List.mem_cons_self ..)
  have hG := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hU := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have h2 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..))))
  simp only [cv_append, cv_invRev, cv_zword, pow_zero, one_mul, mul_one] at hF hG hU
  rw [cv_wpow, cv_zword, pow_zero, pow_zero, one_mul, pow_one, pow_two] at h2
  refine ⟨?_, ?_, ?_, h2⟩
  · rw [← hF]; group
  · rw [← hG]; group
  · calc cv (alphaU liftW0) = cv liftW0 * ((cv liftW0)⁻¹ * cv (alphaU liftW0)) := by group
      _ = cv liftW0 := by rw [hU, mul_one]

theorem sigma_liftW0 : sigma (cv liftW0) = wordPerm (tg 4) := by
  rw [liftW0, cv_append, cv_append, map_mul, map_mul, sigma_tw 4 (by norm_num)]
  rw [show cv zOne = z₁ from rfl, show cv zTwo = z₂ from rfl, sigma_z₁, sigma_z₂, mul_one,
    mul_one]

theorem conj_r_mem_T0 :
    (∀ t ∈ T0, r₂ * t * r₂⁻¹ ∈ T0) ∧ ∀ t ∈ T0, r₃ * t * r₃⁻¹ ∈ T0 := by
  have h := liftParts.norm
  simp only [liftNormOK, Bool.and_eq_true, allBelow_eq_true] at h
  have hr₂ : TabRep r₂T r₂⁻¹ := by rw [inv_eq_of_mul_eq_one_right r₂_mul_self]; exact tabRep_r₂
  have hr₃ : TabRep r₃T r₃⁻¹ := by rw [inv_eq_of_mul_eq_one_right r₃_mul_self]; exact tabRep_r₃
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := exists_tg ht
    exact mem_of_found_enum enumerates_T0 (tabRep_r₂.conjTab (tabRep_wordTab _) hr₂)
      (h.1 k hk).1
  · obtain ⟨k, hk, rfl⟩ := exists_tg ht
    exact mem_of_found_enum enumerates_T0 (tabRep_r₃.conjTab (tabRep_wordTab _) hr₃)
      (h.1 k hk).2

theorem r₂_mul_r₃ : r₂ * r₃ = r₃ * r₂ := by
  have h := liftParts.norm
  simp only [liftNormOK, Bool.and_eq_true] at h
  exact ((tabRep_r₂.comp tabRep_r₃).beq_iff (tabRep_r₃.comp tabRep_r₂)).1 h.2

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem IsQSetting.q_liftW0 (h : IsQSetting q l) :
    q (l (cv liftW0)) = wordPerm (tg 4) := by
  rw [h.q_l, sigma_liftW0]

theorem IsQSetting.liftW0_mul_self
    (h : IsQSetting q l) : l (cv liftW0) * l (cv liftW0) = 1 := by
  rw [← map_mul, cv_alpha_liftW0.2.2.2, h.lz₃]

theorem IsQSetting.beta_liftW0
    (h : IsQSetting q l) {β : E ≃* E} {ρ : Equiv.Perm (Fin 42)}
    (hρ : ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄) (hβ : ∀ e, q (β e) = ρ * q e * ρ⁻¹) :
    β (l (cv liftW0)) = l (cv liftW0) := by
  obtain ⟨hF, hG, hU, -⟩ := cv_alpha_liftW0
  rcases hρ with rfl | rfl | rfl
  · rw [beta_cv_of h.ker_le h.ql hβ
      (abPerm_conj_of tabRep_r₂ r₂_mul_self tabRep_aS coverParts.autF.1)
      (abPerm_conj_of tabRep_r₂ r₂_mul_self tabRep_bS coverParts.autF.2) liftW0]
    rw [show substWord (autWs uAF uBF) liftW0 = alphaF liftW0 from rfl, hF, map_mul, map_pow, h.lz₃,
      one_pow, mul_one]
  · rw [beta_cv_of h.ker_le h.ql hβ
      (abPerm_conj_of tabRep_r₃ r₃_mul_self tabRep_aS coverParts.autG.1)
      (abPerm_conj_of tabRep_r₃ r₃_mul_self tabRep_bS coverParts.autG.2) liftW0]
    rw [show substWord (autWs uAG uBG) liftW0 = alphaG liftW0 from rfl, hG, map_mul, map_pow, h.lz₃,
      one_pow, mul_one]
  · rw [beta_cv_of h.ker_le h.ql hβ
      (abPerm_conj_of tabRep_r₄ r₄_mul_self tabRep_aS coverParts.autU.1)
      (abPerm_conj_of tabRep_r₄ r₄_mul_self tabRep_bS coverParts.autU.2) liftW0]
    rw [show substWord (autWs uAU uBU) liftW0 = alphaU liftW0 from rfl, hU]

end CFSG.ComponentClassification.GrSLit.L34Facts
