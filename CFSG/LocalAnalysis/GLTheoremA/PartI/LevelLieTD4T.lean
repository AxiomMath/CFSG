module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieG2ELev

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.I1420 CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E

private theorem lieRowTD4_nonab {S : Type} [Group S] [IsSimpleGroup S]
    (hc : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := S)).1 ‹IsSimpleGroup S›)


theorem kdLieRowTD4Two_holds : KDLieRowTD4Two := by
  intro q hv hq
  obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.trialityD4 q, hv⟩
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := hfin
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := hsimp
  have hcard : Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group = 211341312 := by
    have h := lieOrderBridge_holds ⟨.trialityD4 q, hv⟩
      (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group ⟨MulEquiv.refl _⟩
    rw [h]
    simp only [lieOrderFormula, orderTrialityD4, hq]
    norm_num
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group, a * b ≠ b * a :=
    lieRowTD4_nonab (by rw [hcard]; norm_num)
  refine downLe_of_chev2 hnc ⟨.trialityD4 q, hv⟩ (MulEquiv.refl _)
    (by simpa using primePower_p_eq Nat.prime_two one_ne_zero (by simpa using hq)) ?_ ?_ ?_
  · rw [hcard]
    unfold Nbig
    norm_num
  · exact kLevel_le_two_of_k2 ⟨TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩, ⟨rfl, hq⟩,
      ⟨MulEquiv.refl _⟩⟩
  · rintro β - - ⟨-, h73⟩
    have h := h73.trans (Subgroup.card_subgroup_dvd_card (fixSubgroup β))
    rw [hcard] at h
    omega

end CFSG.LocalAnalysis.GLTheoremA
