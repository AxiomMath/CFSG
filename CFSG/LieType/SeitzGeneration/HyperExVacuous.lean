module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TitsP3NoElemAbelian
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ExcPlaneG2Three
public import CFSG.LieType.SeitzGeneration.HyperExParabolic
public import CFSG.LieType.SeitzGeneration.HyperExReeType

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge
  CFSG.Open CFSG.AGLEmbedding TauCeti

section Chevalley


theorem excCubeFor_G2 : ExcCubeFor IsG2Index := by
  rintro ⟨d, hv⟩ p hp hp2 hpd - ⟨q, rfl⟩ ⟨E₀, hE₀, hc₀⟩
  exfalso
  have hpq : p ≠ q.p := by simpa using hpd
  rcases eq_three_or_five_le hp hp2 with rfl | hp5
  · exact false_of_rankLE2_of_card hp
      (CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.rankLE2_three_cat_G2 q hv hpq)
      hE₀ hc₀
  · obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hK]
      exact not_dvd_card_of_ne hp hpq
    exact false_of_rankLE2_of_card hp
      (RankLE2.of_injective e.toMonoidHom e.injective (rankLE2_adjointGroup_G2 K hp hp5 hpK))
      hE₀ hc₀

theorem excCubeFor_triality : ExcCubeFor IsTrialityIndex := by
  rintro ⟨d, hv⟩ p hp hp2 hpd - ⟨q, rfl⟩ ⟨E₀, hE₀, hc₀⟩
  exfalso
  have hpq : p ≠ q.p := by simpa using hpd
  rcases eq_three_or_five_le hp hp2 with rfl | hp5
  · exact false_of_rankLE2_of_card hp
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv hpq.symm)
      hE₀ hc₀
  · exact false_of_rankLE2_of_card hp
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_cat_trialityD4 q hv hp hp5 hpq) hE₀ hc₀

end Chevalley

section ReeType


theorem hyperExReeTypeThree : HyperExReeTypeThree := by
  rintro ⟨d, hv⟩ p hp hp2 hpd - ⟨E₀, hE₀, hc₀, hd, rfl⟩
  exfalso
  rcases hd with ⟨m, rfl⟩ | rfl
  · exact false_of_rankLE2_of_card hp
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_reeF4 hv) hE₀ hc₀
  · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.no_elemAbelian27_cat_tits hv hE₀
      (by rw [hc₀]; norm_num)

end ReeType

end CFSG.LieType.SeitzGeneration
