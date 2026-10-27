module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AS
import CFSG.ClassicalInvolution.Balance.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {E F1 F2 : Subgroup G}

theorem sec8t84g3a_gamma_Q {γ : G} (hE : E.map (MulAut.conj γ).toMonoidHom = F1 ⊔ F2)
    (hE0 : (F1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = E) :
    γ ∈ normalizer (sec8t84g_Q E (F1 ⊔ F2) : Set G) ∧
      γ ∈ normalizer (oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) : Set G) ∧
      γ ∈ normalizer ((E ⊔ (F1 ⊔ F2) : Subgroup G) : Set G) := by
  set c : G ≃* G := MulAut.conj γ with hc
  have hinj : Function.Injective c.toMonoidHom := c.injective
  have hQ : (sec8t84g_Q E (F1 ⊔ F2)).map c.toMonoidHom = sec8t84g_Q E (F1 ⊔ F2) := by
    unfold sec8t84g_Q
    rw [Subgroup.map_inf _ _ _ hinj, Subgroup.map_equiv_normalizer_eq,
      Subgroup.map_equiv_normalizer_eq, hE, hE0, inf_comm]
  refine ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hQ, ?_, ?_⟩
  · have hOle : (oddCoreIn (sec8t84g_Q E (F1 ⊔ F2))).map c.toMonoidHom ≤
        oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) := by
      apply CFSG.ClassicalInvolution.Balance.le_oddCoreIn_of_normalizes
      · calc (oddCoreIn (sec8t84g_Q E (F1 ⊔ F2))).map c.toMonoidHom
            ≤ (sec8t84g_Q E (F1 ⊔ F2)).map c.toMonoidHom :=
              Subgroup.map_mono (CFSG.ClassicalInvolution.Balance.oddCoreIn_le _)
          _ = sec8t84g_Q E (F1 ⊔ F2) := hQ
      · intro q hq
        have h1 := Subgroup.map_equiv_normalizer_eq (oddCoreIn (sec8t84g_Q E (F1 ⊔ F2))) c
        have h2 : (sec8t84g_Q E (F1 ⊔ F2)).map c.toMonoidHom ≤
            (normalizer (oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) : Set G)).map c.toMonoidHom :=
          Subgroup.map_mono (CFSG.ClassicalInvolution.Balance.normalizer_oddCoreIn _)
        rw [hQ, h1] at h2
        exact h2 hq
      · rw [Subgroup.card_map_of_injective hinj]
        exact CFSG.ClassicalInvolution.Balance.odd_card_oddCoreIn _
    have hOeq := Subgroup.eq_of_le_of_card_ge hOle
      (le_of_eq (Subgroup.card_map_of_injective hinj).symm)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hOeq
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    erw [hE, hE0]
    exact sup_comm _ _

end CFSG.OddStandard.SmallF3.Omega
