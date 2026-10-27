module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineOne
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

namespace NineEightFour

theorem relPPrimeCore_eq_map {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    relPPrimeCore p C = (primeComplementCore (G := ↥C) p).map C.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNC, hNn, hNc⟩ := hN
    have h1 : N.subgroupOf C ≤ primeComplementCore (G := ↥C) p := by
      refine le_sSup ⟨hNn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hNc
    calc N = (N.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hNC).symm
      _ ≤ _ := Subgroup.map_mono h1
  · refine le_sSup ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · show (Subgroup.comap C.subtype
          ((primeComplementCore (G := ↥C) p).map C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card

theorem standingGen_of_setting (hS : Setting G) : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G :=
  ⟨hS.simple, hS.nonab, hS.kProper, hS.charTwo, hS.rank.symm.le⟩

theorem exists_nineCore {p : ℕ} {P : Sylow p G} {M H₁ R₁ H₀ Q₀ : Subgroup G} (hS : Setting G)
    (he : D1Escape p P M H₁ R₁) (hQ : IsAGLQ p M Q₀) (hQH : Q₀ ≤ H₀)
    (hH₀ : GLBIsMaxTwoLocal H₀) (hH₀M : ¬ H₀ ≤ M) :
    ∃ (k : ℕ) (E : Subgroup G), AGL81C.NineCore G M p Q₀ H₀ E k := by
  haveI := hS.simple
  obtain ⟨k, E, hE⟩ := exists_isStdE_of_isAGLQ he hQ
  exact ⟨k, E, standingGen_of_setting hS, he.maxTwoLocal_M, he.prime, he.ne_two, hQ.1, hQ.2.1,
    ⟨twoLocal_ne_top hS.nonab _ hH₀.1, hQH, hH₀M⟩, hE⟩

end NineEightFour

theorem agl81NineEightFour_holds : AGL81NineEightFour G := by
  intro hS p P M H₁ R₁ he H₀ Q₀ hQ hQH hH₀ hH₀M _ hb3
  haveI : Fact p.Prime := ⟨he.prime⟩
  obtain ⟨k, E, hcore⟩ := NineEightFour.exists_nineCore hS he hQ hQH hH₀ hH₀M
  have h3 : pCoreOf 2 (H₀ ⊓ M) = pCoreOf 2 H₀ := by
    by_cases hJ : AGL81C.pLayerIn p H₀ ≤ M
    · exact hcore.nineEight_one hJ
    have hO : (primeComplementCore (G := H₀) p).map H₀.subtype ≤ M := by
      rw [← NineEightFour.relPPrimeCore_eq_map he.prime]
      exact hcore.relPPrimeCore_le
    exact hcore.nineEight_three_of_le (sSup_invTwoSubgroups_le_xSub hJ hO hb3)
  have hle : pCoreOf 2 H₀ ≤ M := h3 ▸ (pCoreOf_le 2 _).trans inf_le_right
  have hpair : TwoLocalPair M H₀ := ⟨he.maxTwoLocal_M, hH₀, hH₀M, hle⟩
  exact ⟨h3, hpair.twoCore_M_le h3, hle⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
