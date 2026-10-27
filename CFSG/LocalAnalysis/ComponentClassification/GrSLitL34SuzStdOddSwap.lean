module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapZero
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapNonzero

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

theorem l34SuzOddSwappedExclusion_of_inputs
    (h5 : GSThmB.AschbacherTheorem5Input) (hKG : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hAut2A : SuzTwoACentralizerAutExtension) (h2AF : SuzTwoAFusion)
    (h2AC : SuzTwoACentralizerFacts) (hRig : SuzTwoBRootRigidity) (hZ : L34SuzOddZeroStar) :
    L34SuzOddSwappedExclusion := by
  intro G _ _ A V K t y hS hD hsw
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V, u ≠ 1 := by
    rcases V.bot_or_exists_ne_one with h | h
    · have h4 := hD.card_V
      rw [h, Subgroup.card_bot] at h4
      exact absurd h4 (by norm_num)
    · exact h
  obtain ⟨P, hc, hPu, hcomp, hne, hK⟩ := hsw u hu hu1
  by_cases hfix : ∀ v ∈ V, P.map (MulAut.conj v).toMonoidHom = P
  · exact false_of_forall_map_conj_eq_of_l34SuzOdd h5 hKG hZ hS hD hu hu1 hc hPu hcomp hne hK
      hfix
  · push Not at hfix
    obtain ⟨v, hv, hvP⟩ := hfix
    have hE := sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD (mem_sup_left hv)
    rcases map_conj_eq_or_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK
        (mul_comm_of_mem_of_l34SuzOdd hD hv hu) (mem_centralizer_singleton_iff.mp hE.1) hE.2 with
      h | h
    · exact absurd h hvP
    · exact false_of_map_conj_eq_map_of_l34SuzOdd hAut2A h2AF h2AC hRig hS hD hu hu1 hc hPu hcomp
        hne hK hv h

end CFSG.ComponentClassification.GrSLit.L34Sec5S
