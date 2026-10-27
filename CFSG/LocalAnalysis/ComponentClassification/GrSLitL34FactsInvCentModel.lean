
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCentModelBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCentModelBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsEights

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

section Witness

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem beta_cv_of
    (hker : q.ker ≤ center E)
    (hl : q.comp l = sigma) {β : E ≃* E} {ρ : Equiv.Perm (Fin 42)}
    (hβ : ∀ e, q (β e) = ρ * q e * ρ⁻¹) {uA uB : List (Fin 2 × Bool)}
    (hA : abPerm uA = ρ * aS * ρ⁻¹) (hB : abPerm uB = ρ * bS * ρ⁻¹) (w : List (Fin 2 × Bool)) :
    β (l (cv w)) = l (cv (substWord (autWs uA uB) w)) := by
  obtain ⟨α, hα, hσα⟩ := exists_autLift ρ hA hB
  have hql : ∀ c, q (l c) = sigma c := fun c => by rw [← MonoidHom.comp_apply, hl]
  have hext : β.toMonoidHom.comp l = l.comp α := by
    apply hom_ext_of_central commutator_cover q hker
    refine MonoidHom.ext fun c => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hβ, hql, hql, hσα]
  have := DFunLike.congr_fun hext (cv w)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
  rw [this, hα]

theorem fixed_involution_of
    (h : IsQSetting q l) {β : E ≃* E} {w a : List (Fin 2 × Bool)} {k m : ℕ}
    (hβw : β (l (cv w)) = l (cv a)) (h1 : cv (FreeGroup.invRev w ++ a) = cv (zword 0 0 k))
    (h2 : cv (wpow w 2) = cv (zword 0 0 m)) (hw : abTab w ≠ idTab 42) :
    β (l (cv w)) = l (cv w) ∧ l (cv w) * l (cv w) = 1 ∧ q (l (cv w)) ≠ 1 := by
  have h3 := h.lz₃
  refine ⟨?_, ?_, ?_⟩
  · have e1 := congrArg l h1
    rw [cv_append, cv_invRev, map_mul, map_inv, cv_zword, map_mul, map_mul, map_pow, map_pow,
      map_pow, h3, one_pow, mul_one, pow_zero, pow_zero, mul_one, inv_mul_eq_one] at e1
    rw [hβw, ← e1]
  · have e2 := congrArg l h2
    rw [cv_wpow, map_pow, cv_zword, map_mul, map_mul, map_pow, map_pow, map_pow, h3, one_pow,
      mul_one, pow_zero, pow_zero, mul_one, pow_two] at e2
    exact e2
  · intro h1'
    rw [h.q_l, sigma_cv] at h1'
    exact hw ((tabRep_abTab w).tab_eq (h1' ▸ TabRep.idTab))

theorem IsQSetting.exists_witness
    (h : IsQSetting q l)
    {β : E ≃* E} {ρ : Equiv.Perm (Fin 42)} (hρ : ρ = r₂ ∨ ρ = r₃ ∨ ρ = r₄)
    (hβ : ∀ e, q (β e) = ρ * q e * ρ⁻¹) :
    ∃ w : E, β w = w ∧ w * w = 1 ∧ q w ≠ 1 := by
  rcases hρ with rfl | rfl | rfl
  · have s1 := cv_spec (spec_mem (s := (FreeGroup.invRev witnessF ++ alphaF witnessF, 0, 0, 0))
      List.mem_cons_self)
    have s2 := cv_spec (spec_mem (s := (wpow witnessF 2, 0, 0, 0))
      (List.mem_cons_of_mem _ List.mem_cons_self))
    exact ⟨_, fixed_involution_of h (beta_cv_of h.ker_le h.ql hβ
      (abPerm_conj_of tabRep_r₂ r₂_mul_self tabRep_aS coverParts.autF.1)
      (abPerm_conj_of tabRep_r₂ r₂_mul_self tabRep_bS coverParts.autF.2) witnessF) s1 s2
      (abTab_ne_of_witnessOK coverParts.witF)⟩
  · have s1 := cv_spec (spec_mem (s := (FreeGroup.invRev witnessG ++ alphaG witnessG, 0, 0, 1))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    have s2 := cv_spec (spec_mem (s := (wpow witnessG 2, 0, 0, 2))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))))
    exact ⟨_, fixed_involution_of h (beta_cv_of h.ker_le h.ql hβ
      (abPerm_conj_of tabRep_r₃ r₃_mul_self tabRep_aS coverParts.autG.1)
      (abPerm_conj_of tabRep_r₃ r₃_mul_self tabRep_bS coverParts.autG.2) witnessG) s1 s2
      (abTab_ne_of_witnessOK coverParts.witG)⟩
  · have s1 := cv_spec (spec_mem (s := (FreeGroup.invRev witnessU ++ alphaU witnessU, 0, 0, 0))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))))
    have s2 := cv_spec (spec_mem (s := (wpow witnessU 2, 0, 0, 0))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
    exact ⟨_, fixed_involution_of h (beta_cv_of h.ker_le h.ql hβ
      (abPerm_conj_of tabRep_r₄ r₄_mul_self tabRep_aS coverParts.autU.1)
      (abPerm_conj_of tabRep_r₄ r₄_mul_self tabRep_bS coverParts.autU.2) witnessU) s1 s2
      (abTab_ne_of_witnessOK coverParts.witU)⟩

theorem IsQSetting.comm_i8
    (h : IsQSetting q l) {e₀ : E}
    (he₀ : q e₀ = 1 ∨ q e₀ = wordPerm (tg 4)) :
    e₀ * ilift l (8, 1, 0, 0) = ilift l (8, 1, 0, 0) * e₀ := by
  rcases he₀ with he | he
  · exact (mem_center_iff.mp (h.ker_le he) _).symm
  · have hq4 : q (ilift l (4, 1, 1, 1)) = wordPerm (tg 4) := h.q_ilift (by norm_num)
    have hc48 : ilift l (4, 1, 1, 1) * ilift l (8, 1, 0, 0) =
        ilift l (8, 1, 0, 0) * ilift l (4, 1, 1, 1) :=
      h.ilift_comm (by
        rw [← map_mul, cv_comm_of_commData (d := (4, 8, 0, 0, 0)) (by decide) rfl, map_mul])
    have hz : (ilift l (4, 1, 1, 1))⁻¹ * e₀ ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hq4, he, inv_mul_cancel]
    have hzc := mem_center_iff.mp (h.ker_le hz)
    have he' : e₀ = ilift l (4, 1, 1, 1) * ((ilift l (4, 1, 1, 1))⁻¹ * e₀) := by group
    rw [he']
    generalize (ilift l (4, 1, 1, 1))⁻¹ * e₀ = z at hzc
    calc ilift l (4, 1, 1, 1) * z * ilift l (8, 1, 0, 0) =
        ilift l (4, 1, 1, 1) * (ilift l (8, 1, 0, 0) * z) := by rw [mul_assoc, hzc]
      _ = ilift l (8, 1, 0, 0) * ilift l (4, 1, 1, 1) * z := by rw [← mul_assoc, hc48]
      _ = ilift l (8, 1, 0, 0) * (ilift l (4, 1, 1, 1) * z) := by group

end Witness

variable {G : Type} [Group G]

end CFSG.ComponentClassification.GrSLit.L34Facts
