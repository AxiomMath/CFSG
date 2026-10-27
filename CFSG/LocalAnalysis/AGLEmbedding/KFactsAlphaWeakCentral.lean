module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeak
public import CFSG.LocalAnalysis.AGLEmbedding.KlingenRoute
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank

namespace ReducedNongeneration

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem outTwo_of_mem_of_kFactAlphaW (h : ReducedNongeneration p X R X₀)
    (hR4 : 4 ≤ Open.pRank p (R : Subgroup X)) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = p) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) (hKF : KFactAlphaW) :
    (∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p →
        c ∈ Subgroup.zpowers z) ∧
      KOutTwoGroup K ∧
      ((∃ A : Subgroup X, A ≤ (R : Subgroup X) ⊓ K ∧
          A ≤ Subgroup.centralizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ∧
          IsElemAbelian p A ∧ Nat.card A = p ^ 2) ∨
        ((∀ t ∈ (R : Subgroup X) ⊓ K, t ^ p = 1) ∧
          Open.pRank p ((R : Subgroup X) ⊓ K) ≤ 3) ∨
        (∃ A : Subgroup X, A ≤ (R : Subgroup X) ⊓ K ∧
          (R : Subgroup X) ⊓ K ≤ Subgroup.normalizer (A : Set X) ∧ IsElemAbelian p A ∧
          p ^ (p + 1) ≤ Nat.card A)) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hnc := h.not_isCyclic_inf_of_mem hz hzp hK hzK
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  refine ⟨h.mem_zpowers_of_mem_inf_centralizer hz hzp hK hKn hzK, ?_⟩
  rcases hKF K hK.2.2 (hX.isCatalogGroup_center_quotient hK) p hp h.ne_two
      (center_ne_bot_of_mem hp hz hzp hzK) (isPGroup_center_of_isComponentOf hp h.core_eq_bot hK)
      (h.isCyclic_center hK hKn) T with
    ⟨hgen, h3 | hout⟩ | ⟨hgen, hZ3, hout⟩ | hb | ⟨hc, h3⟩ | ⟨h2, hd⟩
  · exact (h.false_of_three_le_pRank_of_le hKn (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen)
      h3).elim
  · exact (h.false_of_kOutNormalSylow (h.le_of_kGenThree hR4 hz hzp hK hKn hzK hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout).elim
  · exact (h.false_of_kOutNormalSylow (h.le_of_kGenTwoModAbFix hz hzp hK hKn hzK hZ3 hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout).elim
  · exact (h.false_of_pRank_mulAut_le_two hR4 hz hzp hK hKn hzK hb).elim
  · exact (h.false_of_three_le_pRank_of_le hKn (le_of_weakCore_eq_top h T hT hc) h3).elim
  · refine ⟨h2, ?_⟩
    rw [← hT]
    rcases hd with hd | hd | hd
    · exact Or.inl (exists_map_of_exists_centralizer hd)
    · exact Or.inr (Or.inl (pow_and_pRank_map hp hd))
    · exact Or.inr (Or.inr (exists_map_of_exists_normalizer hd))

end ReducedNongeneration

theorem d1ConstrainedCase_of_kFactsW (hβ : KFactBeta) (hα : KFactAlphaW) :
    D1ConstrainedCase := by
  intro G _ _ hglob p P M hloc H R h hcon
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨X, _, _, Rbar, X₀, zbar, hred, hR4, hX, hz, hzp, hzR, ⟨K, hK, hKn⟩,
    ⟨v, hvR, hvp, hv⟩, E, L, hER, hEcard, hEexp, hEZ, e, hSL⟩ :=
    h.exists_reduced_centralizer_data hglob hloc hcon
  by_cases hzK : zbar ∈ K
  · obtain ⟨hC, hout, he⟩ := hred.outTwo_of_mem_of_kFactAlphaW hR4 hX hz hzp hK hKn hzK hα
    exact false_of_outTwo hred.prime hred.ne_two Rbar hR4 (mem_sylow_of_mem_center hz hzp Rbar)
      hzK hzp hzR hC hout hvR hvp hv he
  · obtain ⟨hZK, hcyc, hfacts⟩ := hred.rankOneLieAutFacts_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
    exact false_of_rankOneLieAutFacts hred.ne_two hZK hfacts hEcard hEexp
      (inf_centralizer_eq_center_map_of_isCyclic hER hEexp hEZ hz hzp hcyc) e hSL

theorem false_of_centralizerInput_of_kFactsW (hβ : KFactBeta) (hα : KFactAlphaW) {G : Type}
    [Group G] [Finite G] (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hK : Open.IsKProper G) {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G} {z : G}
    (h : D1CentralizerInput p P M z) : False := by
  obtain ⟨X, _, _, Rbar, X₀, zbar, hred, hR4, hX, hz, hzp, hzR, ⟨K, hK, hKn⟩,
    ⟨v, hvR, hvp, hv⟩, E, L, hER, hEcard, hEexp, hEZ, e, hSL⟩ :=
    h.exists_reduced_centralizer_data hs hnab hK
  by_cases hzK : zbar ∈ K
  · obtain ⟨hC, hout, he⟩ := hred.outTwo_of_mem_of_kFactAlphaW hR4 hX hz hzp hK hKn hzK hα
    exact false_of_outTwo hred.prime hred.ne_two Rbar hR4 (mem_sylow_of_mem_center hz hzp Rbar)
      hzK hzp hzR hC hout hvR hvp hv he
  · obtain ⟨hZK, hcyc, hfacts⟩ := hred.rankOneLieAutFacts_of_not_mem hR4 hX hz hzp hK hKn hzK hβ
    exact false_of_rankOneLieAutFacts hred.ne_two hZK hfacts hEcard hEexp
      (inf_centralizer_eq_center_map_of_isCyclic hER hEexp hEZ hz hzp hcyc) e hSL

theorem d1_of_kFactsW_of_componentCaseInd (hβ : KFactBeta) (hα : KFactAlphaW)
    (hcomp : D1ComponentCaseInd) (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : Open.IsKProper G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) (hpre : GLBPreuniqueness G) (p : ℕ) (hp : p ∈ GLBBetaFour G)
    (P : Sylow p G) (M : Subgroup G) (hM : GLBIsMaxTwoLocal M)
    (hWM : GLBWeakCore p (P : Subgroup G) ≤ M) (H : Subgroup G) (hH : IsTwoLocal H)
    (hHM : 3 ≤ Open.pRank p (H ⊓ M)) : H ≤ M :=
  d1_of_cases_ind (d1ConstrainedCase_of_kFactsW hβ hα) hcomp G hnonab hK hchar he hpre p hp P M
    hM hWM H hH hHM

theorem d1CaseThree_of_notKlingen_of_kFactsW (hβ : KFactBeta) (hα : KFactAlphaW)
    (h : D1CaseThreeNotKlingen) : D1CaseThree := by
  intro G _ _ p P M H R Rbar hcfg K hK huniq hnc hcent
  have : Fact p.Prime := ⟨hcfg.ext.prime⟩
  by_cases hKD : HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
  · obtain ⟨z, hz⟩ := hcfg.ext.centralizerInput_of_klingen hcfg.loc Rbar hcfg.rbar hKD
    exact false_of_centralizerInput_of_kFactsW hβ hα hcfg.glob.simple hcfg.glob.nonab
      hcfg.glob.kProper hz
  · exact h G p P M H R Rbar hcfg K hK huniq hnc hcent hKD

end CFSG.AGLEmbedding
