module

public import CFSG.LocalAnalysis.AGLEmbedding.CentralizerCase
public import CFSG.LocalAnalysis.AGLEmbedding.GuestPrime

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1ComponentCaseInd : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G →
    ∀ p : ℕ, (∀ q ∈ GLBBetaFour G, q < p → D1At G q) →
    ∀ (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H R : Subgroup G, D1Extremal p P M H R → ¬ HasPrimeConstraint (G := H) p → False

theorem D1ComponentCase.toInd (h : D1ComponentCase) : D1ComponentCaseInd :=
  fun G _ _ hglob p _ P M hloc H R hext hcon => h G hglob p P M hloc H R hext hcon

theorem d1At_of_extremalAt {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p ∈ GLBBetaFour G)
    (h : ∀ (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H R : Subgroup G, D1Extremal p P M H R → False) :
    D1At G p := by
  intro Q M hM hWM H hH hHM
  refine le_of_maxSylowCase hp.1 Q hWM ?_ hH hHM
  intro K hK T hTP hTrank
  by_contra hnot
  obtain ⟨K', R', hext⟩ :=
    (D1Escape.of_maxCase ⟨hp, hM, hWM⟩ hK T hTP hTrank hnot).exists_extremal
  exact h Q M ⟨hp, hM, hWM⟩ K' R' hext

theorem d1At_of_cases_ind (hcon : D1ConstrainedCase) (hcomp : D1ComponentCaseInd) {G : Type}
    [Group G] [Finite G] (hglob : D1Global G) : ∀ p ∈ GLBBetaFour G, D1At G p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    refine d1At_of_extremalAt hp fun P M hloc H R hext => ?_
    by_cases hc : HasPrimeConstraint (G := H) p
    · exact hcon G hglob p P M hloc H R hext hc
    · exact hcomp G hglob p (fun q hq hqp => ih q hqp hq) P M hloc H R hext hc

theorem d1_of_cases_ind (hcon : D1ConstrainedCase) (hcomp : D1ComponentCaseInd) (G : Type)
    [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : IsKProper G) (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G)
    (hpre : GLBPreuniqueness G) (p : ℕ) (hp : p ∈ GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : GLBIsMaxTwoLocal M) (hWM : GLBWeakCore p (P : Subgroup G) ≤ M)
    (H : Subgroup G) (hH : IsTwoLocal H) (hHM : 3 ≤ Open.pRank p (H ⊓ M)) : H ≤ M :=
  d1At_of_cases_ind hcon hcomp ⟨inferInstance, hnonab, hK, hchar, he, hpre⟩ p hp P M hM hWM H
    hH hHM

theorem d1_of_kFacts_of_componentCaseInd (hβ : KFactBeta) (hα : KFactAlpha)
    (hcomp : D1ComponentCaseInd) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : IsKProper G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM : GLBIsMaxTwoLocal M)
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (H : Subgroup G) (hH : IsTwoLocal H)
    (hHM : 3 ≤ Open.pRank p (H ⊓ M)) : H ≤ M :=
  d1_of_cases_ind (d1ConstrainedCase_of_kFacts hβ hα) hcomp G hnonab hK hchar he hpre p hp P M
    hM hWM H hH hHM

end CFSG.AGLEmbedding
