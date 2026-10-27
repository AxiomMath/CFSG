module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Reduction

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (D1Extremal)

variable {G : Type} [Group G] [Finite G]

@[expose] def D1At3 (G : Type) [Group G] [Finite G] (q : ℕ) : Prop :=
  ∀ (Q : Sylow q G) (M : Subgroup G), IsCoreMaxLocal q Q M → ∀ H : Subgroup G, IsTwoLocal H →
    3 ≤ Open.pRank q (H ⊓ M) → H ≤ M

theorem theoremD1_iff_forall_d1At3 : TheoremD1 G ↔ ∀ q ∈ rankThreeSigmaA G, D1At3 G q := by
  refine ⟨fun h q hq Q M hM H hH hrank => ?_, fun h q hq P M hMloc hcore hmax H hH hrank => ?_⟩
  · exact h q hq Q M hM.1.1 hM.2 (fun K hK _ hMK => hM.1.2 K hK hMK) H hH hrank
  · exact h q hq P M ⟨⟨hMloc, fun K hK hMK => hmax K hK (hcore.trans hMK) hMK⟩, hcore⟩ H hH hrank

@[expose] def D1ExtremalAt3 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M → ∀ H R : Subgroup G,
    D1Extremal p P M H R → False

theorem d1ExtremalCase3_iff_forall_extremalAt3 :
    D1ExtremalCase3 G ↔ (Setting G → ∀ p ∈ rankThreeSigmaA G, D1ExtremalAt3 G p) :=
  ⟨fun h hS p hp P M hM H R hext => h hS p hp P M hM H R hext,
    fun h hS p hp P M hM H R hext => h hS p hp P M hM H R hext⟩

theorem d1At3_of_extremalAt3 {q : ℕ} (hq : q ∈ rankThreeSigmaA G) (h : D1ExtremalAt3 G q) :
    D1At3 G q := by
  intro Q M hM H hH hHM
  refine CFSG.AGLEmbedding.le_of_maxSylowCase (sigmaA_prime q hq) Q hM.2 ?_ hH hHM
  intro K hK T hTP hTrank
  by_contra hnot
  obtain ⟨K', R', hext⟩ := (d1Escape_of_maxCase3 hq hM hK T hTP hTrank hnot).exists_extremal
  exact h Q M hM K' R' hext

@[expose] def D1ComponentCaseInd3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ p ∈ rankThreeSigmaA G, (∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q) →
    ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M → ∀ H R : Subgroup G,
      D1Extremal p P M H R → ¬ HasPrimeConstraint (G := H) p → False

end CFSG.LocalAnalysis.RankThreeTheoremC
