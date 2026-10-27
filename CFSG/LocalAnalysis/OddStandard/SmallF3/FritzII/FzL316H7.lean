module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H6b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H6c

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem fzl_str (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 2)
    {T₂ : Subgroup G} (hT : IsFzT2 t x₁ x₂ S T₂)
    {f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4} (hF : FzF t x₁ x₂ f)
    (h37 : Nat.card (fzR t x₁ x₂) = 2 ^ 8 ∧ Nat.card T₂ = 2 ^ 9) :
    FzStr t tau lam rho (fourGrp x₁ x₂) (baseGrp x₁ x₂) (ctxW t x₁ x₂) (fzQ t x₁ x₂ rho)
      (fzR t x₁ x₂) T₂ := by
  have hlamS : lam ∈ S := by
    have hl : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    rw [← h.inf_eq] at hl
    exact hl.1
  have hrho := fzl_rho_Z h
  have hlam := fzl_lam_Z h
  have htau := fzl_tau_facts h hK
  have htf := fzl_t_facts h
  refine
    { ZE := S4A.pt_four_le_base x₁ x₂
      EW := le_sup_right
      WQ := le_sup_left
      QR := fzl_Q_le_R h hK hF
      RT := fzl_R_le_T hT
      card_Z := fzl_card_Z h
      card_E := (h.wreath.baseGrp_eq).2.2
      card_W := fzl_card_W h hK
      card_Q := fzl_card_Q h hK hF
      card_R := by rw [h37.1]; norm_num
      card_T := by rw [h37.2]; norm_num
      pgroup_T := hT.isPGroup
      nrm_Z := fun g hg z hz => fzl_conj_Z h hK (hT.le_N2 hg) hz
      nrm_W := fun g hg w hw => (Subgroup.mem_normalizer_iff.mp (hT.le_N2 hg) w).mp hw
      nrm_Q := fun g hg q hq => fzl_Q_nrm h hK hF g (hT.le_N2 hg) q hq
      nrm_R := fun g hg r hr => fzl_R_normal t x₁ x₂ g (hT.le_N2 hg) r hr
      W_comm := fun a ha b hb => isMulCommutative_iff_of_setLike.mp h.abelian_W a ha b hb
      t_mem := htf.1
      t_sq := htf.2.1
      t_notin_E := fzl_t_notin_E h hK
      W_split := fzl_W_split h hK
      E_exp := fzl_E_exp h hK
      E_sq := fzl_E_sq h hK
      Z_sq := fun z hz => fzl_Z_sq_eq_one h hz
      Z_sqrt := fzl_Z_sqrt h
      E_invol := fzl_E_invol h hK
      E_equiv := fzl_E_equiv h
      CW := fun g hg => by
        have hg' : g ∈ centralizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) :=
          Subgroup.mem_centralizer_iff.mpr fun w hw => (hg w hw).symm
        rwa [h.cent_W] at hg'
      R_comm := fzl_R_comm h hK hF
      R_sq := fzl_R_sq h hK hF
      R_Z := fzl_R_Z h hK
      T_t := fun g hg => fzl_conj_t h hK (hT.le_N2 hg)
      Q_t := fzl_Q_t h hK hF
      tau_R := fzl_tau_R h hK hF
      tau_notin_Q := fzl_tau_notin_Q h hK hF
      tau_t := htau.2.1
      tau_W := htau.2.2.2
      tau_sq := ?_
      tau_Q := fzl_tau_Q h hK hF
      tau_rho := h.tau_rho
      tau_lam := h.tau_lam
      lam_T := hT.S_le hlamS
      lam_sq := hlam.2.2.1
      lam_t := hlam.2.1
      lam_Z := ?_
      lam_E := fzl_lam_E h
      lam_Q := fzl_lam_Q h hK hF
      lam_rho := (fzl_lam_rho h).1
      rho_ord := hrho.2.2.1
      rho_t := hrho.2.1
      rho_nrm_Z := fun z hz => fzl_conj_Z h hK hrho.1 hz
      rho_nrm_E := fzl_rho_nrm_E h
      rho_nrm_Q := fun q hq => fzl_Q_nrm h hK hF rho hrho.1 q hq
      rho_Z := hrho.2.2.2
      rho_Q := fzl_rho_Q h hK hF
      rho_QW := fzl_rho_QW h hK hF
      E_rho := h.comm_rho }
  · rcases fzl_twoCore_cases h hK _ h.tau_sq_mem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  · refine ⟨x₁ ^ 2, Subgroup.subset_closure (by simp), ?_⟩
    rw [hlam.2.2.2.1]
    exact (fzl_z1_ne_z2 h).1.symm

end CFSG.OddStandard.SmallF3.FritzII
