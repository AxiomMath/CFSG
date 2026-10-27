module

public import CFSG.LocalAnalysis.AGLEmbedding.CentralizerTransport
public import CFSG.LocalAnalysis.AGLEmbedding.CentralBeta
public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlpha
public import CFSG.LocalAnalysis.AGLEmbedding.CentralAlphaOut
public import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutomizer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem d1ConstrainedCase_of_kFacts (hβ : KFactBeta) (hα : KFactAlpha) : D1ConstrainedCase := by
  intro G _ _ hglob p P M hloc H R h hcon
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨X, _, _, Rbar, X₀, zbar, hred, hR4, hX, hz, hzp, hzR, ⟨K, hK, hKn⟩,
    ⟨v, hvR, hvp, hv⟩, E, L, hER, hEcard, hEexp, hEZ, e, hSL⟩ :=
    h.exists_reduced_centralizer_data hglob hloc hcon
  by_cases hzK : zbar ∈ K
  · obtain ⟨hC, hout, he⟩ := hred.outTwo_of_mem hR4 hX hz hzp hK hKn hzK hα
    exact false_of_outTwo hred.prime hred.ne_two Rbar hR4 (mem_sylow_of_mem_center hz hzp Rbar)
      hzK hzp hzR hC hout hvR hvp hv he
  · obtain ⟨hZK, hcyc, hfacts⟩ := hred.rankOneLieAutFacts_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
    exact false_of_rankOneLieAutFacts hred.ne_two hZK hfacts hEcard hEexp
      (inf_centralizer_eq_center_map_of_isCyclic hER hEexp hEZ hz hzp hcyc) e hSL

theorem d1_of_kFacts_of_componentCase (hβ : KFactBeta) (hα : KFactAlpha)
    (hcomp : D1ComponentCase) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : IsKProper G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM : GLBIsMaxTwoLocal M)
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (H : Subgroup G) (hH : IsTwoLocal H)
    (hHM : 3 ≤ Open.pRank p (H ⊓ M)) : H ≤ M :=
  d1_of_cases (d1ConstrainedCase_of_kFacts hβ hα) hcomp G hnonab hK hchar he hpre p hp P M hM hWM
    H hH hHM

end CFSG.AGLEmbedding
