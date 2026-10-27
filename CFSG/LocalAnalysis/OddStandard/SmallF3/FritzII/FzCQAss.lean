module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCQDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCP
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCKf

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem fzc_qfacts_of_steps (hs : FzCSteps t L S x₁ x₂ lam rho) :
    FzCQFacts t S x₁ x₂ lam rho where
  card_K := fzc_card_K hs
  K_two := fzc_K_two hs
  K_four := fzc_K_four hs
  card_W := fzc_card_W hs
  not_conj_z := hs.fusion.not_conj_z
  S_le_N2 := fzc_S_le_N2 hs
  V_isFzT2 := fzc_V_isFzT2 hs
  card_V := hs.card_V
  W_le_R := fzc_W_le_R hs
  card_R := fzc_card_R hs
  R_le_V := fzc_R_le_V hs
  V_eq := fzc_V_eq hs
  lam_not_mem_R := fzc_lam_not_mem_R hs
  Q_eq := fzc_Q_eq hs
  R_eq_PK := fzc_R_eq_PK hs
  cent_R_rho := fzc_cent_R_rho hs
  rho_norm_R := fun _ hx => fzc_rho_norm_R hs hx
  lam_norm_R := fun _ hx => fzc_lam_norm_R hs hx
  rho_norm_P := fun _ hx => fzc_rho_norm_P hs hx
  lam_norm_P := fun _ hx => fzc_lam_norm_P hs hx
  P_normal_R := fun _ hr _ hx => fzc_P_normal_R hs hr hx
  R_act_t := fun _ hr => fzc_R_act_t hs hr
  R_orbit_t := fun _ hf => fzc_R_orbit_t hs hf
  cent_R_t := fzc_cent_R_t hs
  R_cent_fourGrp := fun _ hr _ hf => fzc_R_cent_four hs hr hf
  R_sq_mem_W := fun _ hr => fzc_R_sq_mem_W hs hr
  R_comm_le_W := fzc_R_comm_le_W hs
  inf_P_K_of_not_mem := fzc_inf_P_K hs
  card_P_of_not_mem := fzc_card_P hs
  P_fpf_of_not_mem := fun ht _ hx h => fzc_P_fpf hs ht hx h

end CFSG.OddStandard.SmallF3.FritzII
