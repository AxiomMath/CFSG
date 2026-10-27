module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelRad
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelS5
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Link
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Model

theorem Model.modelLinkFacts (ε : Eps) :
    LinkFacts ε (Lm ε) (UQm ε) (QMm ε) (PM ε) (aM ε) (psiM ε) (pM ε) (uM ε) where
  Q_le_U := QMm_le_U
  U_le_P := UQm_le_PM
  P_eq := rfl
  U_pgroup := IsPGroup.of_card (n := 12) (by rw [card_UQm]; norm_num)
  center_U := fun _ hx hc => center_UQm hx hc
  ψ_add := psiM_add
  ψ_inj := psiM_injective
  ψ_mem := psiM_mem_Q
  mem_ψ := fun _ hx => mem_QMm.1 hx
  a_eq := rfl
  p_mem := fun i => PQm_le_PM (pM_mem_P i)
  p_act := pM_act
  P_le := by
    rw [← PQm_eq_PM, PQm_eq]
    exact closure_mono (Set.union_subset_union_left _ (by
      rintro _ ⟨j, rfl⟩
      exact psiM_mem_Q _))
  card_P := card_PM
  S5 := fun _ hAU hAn hAc hA2 hA64 => S5_model hAU hAn hAc hA2 hA64
  u_mem := uM_mem_U
  u_act := uM_act
  U_le := by
    rw [UQm_eq]
    exact closure_mono (Set.union_subset_union_left _ (by
      rintro _ ⟨j, rfl⟩
      exact psiM_mem_Q _))
  U_max := fun _ hVL hV hUV => UQm_max hVL hV hUV
  cent_Q := fun _ hl hc => mem_QMm_of_commute hl hc

variable {G : Type*} [Group G]

end CFSG.EvenSmallLie.OmegaEight.Stage1
