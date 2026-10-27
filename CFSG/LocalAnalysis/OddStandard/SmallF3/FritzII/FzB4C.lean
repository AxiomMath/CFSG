module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB4A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB4B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB2B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H5

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzbs_str_of_ctx
    [IsSimpleGroup G] (h : Ctx t L S x₁ x₂ lam rho tau)
    (hK : Nat.card (twoCore t) = 4) {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f)
    {T₂ : Subgroup G} (hT : IsFzT2 t x₁ x₂ S T₂) {q : G} (hq : zpowers q = twoCore t) :
    FzbsStr t q tau lam rho (x₁ * x₂) (fourGrp x₁ x₂) (baseGrp x₁ x₂) (fzbsX t x₁ x₂)
      (ctxW t x₁ x₂) (fzR t x₁ x₂) T₂ := by
  have hX := fzbs_X_le h
  have hqK : q ∈ twoCore t := hq ▸ mem_zpowers q
  have htt : t * t = 1 := S4A.t_mul_self h.hyp
  have hrhoN : rho ∈ fzN2 t x₁ x₂ := (fzl_rho_Z h).1
  have hlamN : lam ∈ fzN2 t x₁ x₂ := (fzl_lam_Z h).1
  have hRN : ∀ r ∈ fzR t x₁ x₂, r ∈ fzN2 t x₁ x₂ := fun r hr => fzl_R_le_N2 t x₁ x₂ hr
  have hlamS : lam ∈ S := by
    have hlam : lam ∈ wreathGrp x₁ x₂ lam := subset_closure (by simp)
    rw [← h.inf_eq] at hlam
    exact (Subgroup.mem_inf.mp hlam).1
  exact
    { ZE := hX.2.1
      EX := hX.2.2.1
      XW := hX.2.2.2
      WR := fzbs_W_le_R h hF
      RT := fzl_R_le_T hT
      card_Z := fzl_card_Z h
      card_E := h.wreath.baseGrp_eq.2.2
      Z_sq := fun z hz => fzl_Z_sq_eq_one h hz
      E_sq := fun e he => fzbs_E_sq h he
      W_comm := fun a ha b hb =>
        congrArg Subtype.val (isMulCommutative_iff.mp h.abelian_W ⟨a, ha⟩ ⟨b, hb⟩)
      W_invol := fun w hw hw2 => by
        rcases fzbs_invol_W h hw hw2 with hz | ⟨z, hz, rfl⟩
        · exact Or.inl hz
        · right
          rwa [← mul_assoc, htt, one_mul]
      X_iff := fun w hw => fzbs_mem_X_iff h hw
      t_mem := hX.1
      t_sq := (fzl_t_facts h).2.1
      t_notin_E := fzbs_t_not_mem_E h
      X_split := fun x hx => fzbs_X_split h hx
      q_mem := (le_sup_left : twoCore t ≤ ctxW t x₁ x₂) hqK
      q_sq := (fzbs_q_facts h hK hq).2
      W_split := (fzbs_W_cases h hK hq).2
      pgroup_R := fzl_R_isPGroup t x₁ x₂
      R_W := fun r hr w hw => (Subgroup.mem_normalizer_iff.mp (hRN r hr) w).mp hw
      R_X := fun r hr x hx => fzbs_conj_X h (hRN r hr) hx
      R_Z := fzbs_R_Z h
      R_t := fun r hr => by
        obtain ⟨z, hz, hrz⟩ := fzbs_conj_t h (hRN r hr)
        rwa [hrz, ← mul_assoc, htt, one_mul]
      R_t_surj := fun z hz => fzbs_R_t_surj h hK hF hz
      R_fix_t := fun r hr hrt => fzbs_Wtau_cases h hK (fzbs_R_fix_t h hr hrt)
      R_comm := fzbs_R_comm h hF
      R_sq := fzbs_R_sq h hF
      tau_R := fzbs_tau_R h hF
      tau_t := (fzbs_tau_facts h).2.1
      tau_X := (fzbs_tau_facts h).2.2.2.1
      tau_q := fzbs_tau_q h hK hq
      tau_sq := by rw [hq]; exact h.tau_sq_mem
      tau_rho := h.tau_rho
      tau_lam := h.tau_lam
      rho_cube := (fzl_rho_Z h).2.2.1
      rho_R := fun r hr => fzl_R_normal t x₁ x₂ rho hrhoN r hr
      rho_W := fun w hw => (Subgroup.mem_normalizer_iff.mp hrhoN w).mp hw
      rho_X := fun x hx => fzbs_conj_X h hrhoN hx
      rho_E := fzl_rho_nrm_E h
      rho_Z := fun z hz => fzbs_conj_Z h hrhoN hz
      rho_Z_fpf := (fzl_rho_Z h).2.2.2
      rho_t := (fzl_rho_Z h).2.1
      rho_q := fzbs_rho_K h hqK
      rho_W_fix := fun w hw hfix => by rw [hq]; exact fzbs_rho_W_fix h hw hfix
      E_rho := h.comm_rho
      lam_T := hT.S_le hlamS
      lam_sq := (fzl_lam_Z h).2.2.1
      lam_t := (fzl_lam_Z h).2.1
      lam_q := fzbs_lam_K h hqK
      lam_rho := h.lam_rho
      lam_R := fun r hr => fzl_R_normal t x₁ x₂ lam hlamN r hr
      u_mem := mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      u_lam := fzbs_u_lam h
      u_sq_ne := h.wreath.sq_x₁x₂_ne_one
      lam_E_fix := fun e he hfix => fzbs_lam_E_fix h he hfix
      lam_X_inv := fun x hx hinv => fzbs_lam_X_inv h hx hinv
      lam_not_conj := fzbs_lam_not_conj h
      T_cases := fzbs_T2_cases h hK hF hT }

end CFSG.OddStandard.SmallF3.FritzII
