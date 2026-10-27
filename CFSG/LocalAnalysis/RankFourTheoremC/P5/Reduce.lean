module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Plane
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Norm
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry
import CFSG.LieType.SeitzGeneration.ExcPlaneBridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G}

theorem gamma_one_le_of_forall_centralizer_le_p (hG : P5Global G) (hloc : D1Local p P M)
    (hab : IsMulCommutative (P : Subgroup G)) {A : Subgroup G} (hAP : A ≤ (P : Subgroup G))
    (hAe : IsElemAbelian p A)
    (hall : ∀ y ∈ A, y ≠ 1 → centralizer ({y} : Set G) ≤ M) : GLBCore p 1 A ≤ M := by
  have hprime := hp.out
  have hp2 : p ≠ 2 := by
    have := hloc.beta.2.1
    exact this
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  refine (CFSG.PreuniquenessRankFour.Helpers.fullCore_le_iff p 1 A M).2 fun Q hQA hQ1 => ?_
  have hQp : IsPGroup p Q := (elementary_isPGroup p A hAe).to_le hQA
  by_cases hQc : IsCyclic Q
  · obtain ⟨y, hyQ, hy1, hyp, hNQy⟩ := exists_pow_eq_one_normalizer_le_of_isCyclic hprime hQp hQc hQ1
    refine hNQy.trans (normalizer_zpowers_le_of_centralizer_le hG.fc hloc
      (hall y (hQA hyQ) hy1) ?_)
    have h4 : 4 ≤ CFSG.Open.pRank p (P : Subgroup G) := four_le_pRank_sylow hloc.beta P
    have hinf : (P : Subgroup G) ⊓ centralizer ({y} : Set G) = P :=
      inf_of_le_left (PPointFrobenius.pt_P_le_centralizer_of_mem hab (hAP (hQA hyQ)))
    rw [hinf]
    omega
  · have h2 : 2 ≤ CFSG.Open.pRank p Q := two_le_pRank_of_not_isCyclic hprime hp2 hQp hQc
    exact normalizer_le_of_two_le_pRank hG.fc hloc hQp (hQA.trans (hAP.trans hPM)) h2

theorem confinement_of_abelian_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (hType : PTypeHyp p P M) (hab : IsMulCommutative (P : Subgroup G))
    {H : Subgroup G} (hH : IsTwoLocal H) (h2 : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) : H ≤ M := by
  classical
  have hprime := hp.out
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  obtain ⟨R, hRHM, hRe, hRc⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hprime (H ⊓ M)
  obtain ⟨A₀, hA₀R, hA₀e, hA₀c⟩ := CFSG.LieType.SeitzGeneration.exists_isElemAbelian_card_of_le
    (k := 2) hprime hRe (by rw [hRc]; exact Nat.pow_le_pow_right hprime.pos h2)
  have hA₀p : IsPGroup p A₀ := elementary_isPGroup p A₀ hA₀e
  have hA₀HM : A₀ ≤ H ⊓ M := hA₀R.trans hRHM
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM A₀ hA₀p
    (hA₀HM.trans inf_le_right)
  set φ := (MulAut.conj (m : G)).toMonoidHom with hφ
  set A := A₀.map φ with hA
  have hAe : IsElemAbelian p A :=
    elementary_map_injective p A₀ φ (MulAut.conj (m : G)).injective hA₀e
  have hAc : Nat.card A = p ^ 2 := by
    rw [hA, card_map_of_injective (MulAut.conj (m : G)).injective, hA₀c]
  have hAH : A ≤ H.map φ := map_mono (hA₀HM.trans inf_le_left)
  have hAP : A ≤ (P : Subgroup G) := hm
  have hH' : IsTwoLocal (H.map φ) := by
    obtain ⟨T, hT1, hT2, hTH⟩ := hH
    refine ⟨T.map φ, ?_, hT2.map φ, ?_⟩
    · intro h0
      exact hT1 ((map_eq_bot_iff_of_injective (f := φ) T (MulAut.conj (m : G)).injective).mp h0)
    · rw [hTH, Subgroup.map_equiv_normalizer_eq]
  apply (conjugate_subgroup_le_iff_of_conjugator_mem H M (m : G) m.2).1
  by_cases hall : ∀ y ∈ A, y ≠ 1 → centralizer ({y} : Set G) ≤ M
  ·
    have hΓ := gamma_one_le_of_forall_centralizer_le_p hG hloc hab hAP hAe hall
    have hAr : CFSG.Open.pRank p A = 2 := by
      have h1 : 2 ≤ CFSG.Open.pRank p A := CFSG.SectionRank.le_pRank hprime.one_lt le_rfl hAe hAc
      have h3 : CFSG.Open.pRank p A ≤ 2 := by
        refine CFSG.SectionRank.pRank_le hprime.one_lt fun E hEA hE => ?_
        have := Subgroup.card_le_of_le hEA
        rwa [hAc] at this
      omega
    exact hG.d2 p hloc.beta P M hloc.maxLocal (hG.fc p P M hloc) A (elementary_isPGroup p A hAe)
      hAr hΓ (H.map φ) hH' hAH
  ·
    push Not at hall
    obtain ⟨y, hyA, hy1, hyM⟩ := hall
    have hyo : orderOf y = p := orderOf_eq_prime (hAe.2 y hyA) hy1
    have hpt : IsPPoint p P M y := isPPoint_of_mem_abelian hloc hab (hAP hyA) hyo hyM
    exact plane_confinement_p hp5 hK hG hloc hType hpt hAP hAe hAc hyA hH' hAH

end CFSG.LocalAnalysis.RankFourTheoremC.P5
