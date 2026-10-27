module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveN3

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

theorem jankoStep12 : JankoStep12 := by
  intro G _ _ z fr hset hfrs p7 p9 p10 p11
  have h : JankoTwelve.Hyp fr := ⟨hset, hfrs, p7, p9, p10, p11⟩
  exact
    { card_normalizer_N := h.card_normalizer_N
      card_U := h.card_U
      N_le_U := h.N_le_U
      U_inf_centralizer_z := h.U_inf_centralizer_z
      card_U_inf_t := h.card_U_inf_t
      card_U_inf_tz := h.card_U_inf_tz
      center_U := h.center_U
      U_inf_centralizer_ZN := fun _ hx hxS => h.U_inf_centralizer_ZN hx hxS
      isConj_of_mem_M := fun _ hx hxM => h.isConj_s₁_of_mem_M hx hxM
      card_le_of_isConj_s₃ := fun _ hy _ hB hB3 => h.card_le_of_isConj_s₃ hy hB hB3
      normalizer_M := h.normalizer_M
      U_le_normalizer_I := h.U_le_normalizer_I
      centralizer_I := h.centralizer_I
      centralizer_U := h.centralizer_U
      centralizer_S := h.centralizer_S
      K_le_normalizer_U := h.K_le_normalizer_U
      U_inf_K := h.U_inf_K
      K_le_normalizer_I := h.K_le_normalizer_I
      K_le_normalizer_S := h.K_le_normalizer_S
      eq_one_of_le_centralizer := fun _ hk hS => h.eq_one_of_le_centralizer hk hS
      factorization_three := h.factorization_three
      exists_choiceM := h.exists_choiceM }

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
