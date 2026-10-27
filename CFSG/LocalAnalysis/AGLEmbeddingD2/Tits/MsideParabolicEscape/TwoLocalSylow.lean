module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.NormalizerSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.BetaInfSolvable

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.Tits.MsidePrelim

@[expose] def D2L34BetaTwoLocalSylowCyclic : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G] [Finite G] (P : Sylow 3 G)
    (M A H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), D2L34BetaConf d P M A H R Rbar K →
    GLBStronglyEmbedded 3 M → D2L34AllResidue P M → D2L34Kmax H →
    ∀ T : Subgroup G, IsSylowTwoOf T M → ∀ N : Subgroup G, IsTwoLocal N → T ≤ N → ¬ N ≤ M →
      (∀ X : Subgroup G, X ≤ N ⊓ M → IsPGroup 3 X → IsCyclic X) →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥(N ⊓ M) → IsSylowTwoOf T N

theorem d2L34BetaTwoLocalSylow_of_cyclic
    (hSch : KFactCatalogSchreier)
    (hcyc : D2L34BetaTwoLocalSylowCyclic) : D2L34BetaTwoLocalSylow := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax T hT N hN hTN hns
  by_cases hNM : N ≤ M
  · refine ⟨hTN, hT.2.1, fun h => hT.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T N M hTN hNM
    exact h.trans ⟨_, this.symm⟩
  by_cases hcy : ∀ X : Subgroup G, X ≤ N ⊓ M → IsPGroup 3 X → IsCyclic X
  · exact hcyc d G P M A H R Rbar K hc hstr hAll hKmax T hT N hN hTN hNM hcy hns
  · exfalso
    obtain ⟨X, hX, hXp, hXc⟩ : ∃ X : Subgroup G, X ≤ N ⊓ M ∧ IsPGroup 3 X ∧ ¬ IsCyclic X := by
      by_contra h
      exact hcy fun X hX hXp => by
        by_contra hc
        exact h ⟨X, hX, hXp, hc⟩
    exact hns (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.betaConf_isPSolvable_of_le_twoLocal
      hSch hc hstr hAll hN hNM (hX.trans inf_le_left) (hX.trans inf_le_right) hXp hXc le_rfl)

theorem d2L34BetaNormalizerSolvable_of_cyclic
    (hSch : KFactCatalogSchreier)
    (hcov : D2L34BetaPushUpCoverSyl) (hcyc : D2L34BetaTwoLocalSylowCyclic) :
    D2L34BetaNormalizerSolvable :=
  d2L34BetaNormalizerSolvable_of_twoLocalSylow hcov (d2L34BetaTwoLocalSylow_of_cyclic hSch hcyc)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
