module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineTwoOneEscape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.AGLEmbedding (D1Extremal D1Escape D1PhaseThree Asc81bEightFour D1NoXBlock IsWeakSBlock
  d1X0)

variable {G : Type} [Group G] [Finite G]

theorem elevenNineteenItemOne_of_extremal (h74 : AGL81SevenFourTwo) (hOut : KFactOutCyclic)
    (hK3 : KFactsA3 G)
    (hnone : D1ComponentAlphaNone3 G) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hres : D1ConstrainedWeakBlockResidue3 G) (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M H R : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (h : D1Extremal p P M H R) :
    ∃ H₂ : Subgroup G, GLBIsMaxTwoLocal H₂ ∧ ¬ H₂ ≤ M ∧ R ≤ H₂ ∧
      ∃ L : Subgroup (H₂ ⧸ primeComplementCore (G := H₂) p), IsComponentOf L ⊤ ∧
        ¬ L ≤ d1X0 p M H₂ := by
  by_contra hneg
  push Not at hneg
  have : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  have he : D1Escape p P M H R := h.toD1Escape
  have hall : ∀ K : Subgroup G, GLBIsMaxTwoLocal K → R ≤ K → ¬ K ≤ M →
      HasPrimeConstraint (G := K) p := fun K hK hRK hKM =>
    (h.of_maxTwoLocal_ge hK hRK hKM).toD1Escape.hasPrimeConstraint_of_forall_component_le h74
      hOut hS.kProper (hneg K hK hKM hRK)
  have hcon : HasPrimeConstraint (G := H) p := hall H he.maxTwoLocal_H he.le_H he.not_le
  have hcompC : D1CentralizerComponentCase3 G :=
    d1CentralizerComponentCase3_of_cases hK3 d1CentralizerBetaSmallCase3 hnone.centralizer
  have hcompS : D1SylowComponentCase3 G :=
    d1SylowComponentCase3_of_cases hK3 d1SylowBetaSmallCase3 hnone.sylow
  obtain ⟨z, hzR, hz⟩ := exists_centralizerInput3_mem (sylow_le_of_isCoreMaxLocal hS hp hM).2 h hcon
  have hlayer := layer_centralizer_eq_bot hS hp hM h hz hcompC hcompS
  have huniq : ∀ K : Subgroup G, GLBIsMaxTwoLocal K → R ≤ K → ¬ K ≤ M → K = H :=
    fun K hK hRK hKM => hz.eq_of_maxTwoLocal_ge hS hlayer hzR h hall hK hRK hKM
  obtain ⟨hNH, hRP⟩ := h.normalizer_le_and_eq_sylow huniq
  subst hRP
  have hph := h.toPhaseThree3 hS hcon
  obtain ⟨T, hTN, hT2, hTidx, hPT, hST⟩ := h.exists_invariantSylowTwo hS hcon
  obtain ⟨L, hL⟩ := hph.exists_weakSBlock h84 hD2
  obtain ⟨Pbar, zbar, E, C, hEn, e, hdata, hstr⟩ :=
    hz.exists_reducedStructure3 hS.simple hS.nonab hS.kProper hlayer
  exact hres hS p hp P M hM H h inferInstance z hz hlayer Pbar zbar E C hEn e hdata hstr hcon hph
    hzR (hz.centralizer_le_of_eq_sylow hS hlayer h hcon hzR) huniq hNH T hTN hT2 hTidx hPT hST
    (fun U hUT hU hchar => h.normalizer_le_of_char huniq hTN hT2 hTidx hPT hUT hU hchar) L hL

theorem exists_extremal_component_of_extremal (h74 : AGL81SevenFourTwo) (hOut : KFactOutCyclic)
    (hK3 : KFactsA3 G) (hnone : D1ComponentAlphaNone3 G) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hres : D1ConstrainedWeakBlockResidue3 G) (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M H R : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (h : D1Extremal p P M H R) :
    ∃ H₂ : Subgroup G, D1Extremal p P M H₂ R ∧
      ∃ L : Subgroup (H₂ ⧸ primeComplementCore (G := H₂) p), IsComponentOf L ⊤ ∧
        ¬ L ≤ d1X0 p M H₂ := by
  obtain ⟨H₂, hH₂, hH₂M, hRH₂, hL⟩ :=
    elevenNineteenItemOne_of_extremal h74 hOut hK3 hnone h84 hD2 hres hS hp hM h
  exact ⟨H₂, h.of_maxTwoLocal_ge hH₂ hRH₂ hH₂M, hL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
